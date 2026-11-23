import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronSum

noncomputable section

namespace PI.EF

open Finset

def nearB (u T : ℝ) (n : ℕ) : ℝ :=
  if n < ⌊u⌋₊ then (4 * u / T) / ((⌊u⌋₊ : ℝ) - n)
  else if n ≤ ⌊u⌋₊ + 1 then 2 else (4 * u / T) / ((n : ℝ) - ⌊u⌋₊ - 1)

theorem nearB_nonneg {u T : ℝ} (hu : 0 < u) (hT : 0 < T) (n : ℕ) : 0 ≤ nearB u T n := by
  unfold nearB
  have h4 : 0 ≤ 4 * u / T := by positivity
  split_ifs with h1 h2
  · apply div_nonneg h4
    have h5 : (n : ℝ) < ⌊u⌋₊ := by exact_mod_cast h1
    linarith
  · norm_num
  · apply div_nonneg h4
    have h5 : (⌊u⌋₊ : ℝ) + 1 < n := by exact_mod_cast (by omega : ⌊u⌋₊ + 1 < n)
    linarith

theorem sum_inv_le (n : ℕ) : ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have e : ((harmonic n : ℚ) : ℝ) = ∑ j ∈ range n, 1 / ((j : ℝ) + 1) := by
    rw [harmonic]
    push_cast
    simp [one_div]
  rw [← e]
  exact h

theorem sum_nearB (u T : ℝ) :
    ∑ n ∈ range (⌊u⌋₊ + (⌊u⌋₊ + 2)), nearB u T n =
      4 + 2 * ((4 * u / T) * ∑ j ∈ range ⌊u⌋₊, 1 / ((j : ℝ) + 1)) := by
  set n0 := ⌊u⌋₊ with hn0
  rw [Finset.sum_range_add, Finset.sum_range_succ', Finset.sum_range_succ']
  have e1 : ∑ n ∈ range n0, nearB u T n = (4 * u / T) * ∑ j ∈ range n0, 1 / ((j : ℝ) + 1) := by
    rw [← Finset.sum_range_reflect (fun j => 1 / ((j : ℝ) + 1)) n0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n < n0 := Finset.mem_range.mp hn
    have hc : ((n0 - 1 - n : ℕ) : ℝ) + 1 = (n0 : ℝ) - n := by
      have : n0 - 1 - n + 1 = n0 - n := by omega
      have h2 : ((n0 - 1 - n + 1 : ℕ) : ℝ) = ((n0 - n : ℕ) : ℝ) := by rw [this]
      rw [Nat.cast_sub hn'.le] at h2
      rw [← h2]
      push_cast
      ring
    unfold nearB
    rw [if_pos (by rw [← hn0]; exact hn'), hc, ← hn0]
    ring
  have e2 : ∑ i ∈ range n0, nearB u T (n0 + (i + 1 + 1)) =
      (4 * u / T) * ∑ j ∈ range n0, 1 / ((j : ℝ) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold nearB
    rw [← hn0, if_neg (by omega), if_neg (by omega)]
    have : ((n0 + (i + 1 + 1) : ℕ) : ℝ) - n0 - 1 = (i : ℝ) + 1 := by push_cast; ring
    rw [this]
    ring
  have e3 : nearB u T (n0 + (0 + 1)) = 2 := by
    unfold nearB
    rw [← hn0, if_neg (by omega), if_pos (by omega)]
  have e4 : nearB u T (n0 + 0) = 2 := by
    unfold nearB
    rw [← hn0, if_neg (by omega), if_pos (by omega)]
  rw [e1, e2, e3, e4]
  ring

theorem kb_le_div {u T x g : ℝ} (hu : 0 < u) (hT : 0 < T) (hx : 0 < x) (hx2 : x < 2 * u)
    (hg : 0 < g) (h : g ≤ |u - x|) : kb T (u / x) ≤ (4 * u / T) / g := by
  have hlog : g / (2 * u) ≤ |Real.log (u / x)| := by
    rcases le_or_gt x u with hxu | hxu
    · have h1 : 1 - x / u ≤ Real.log (u / x) := by
        have h0 := Real.one_sub_inv_le_log_of_pos (div_pos hu hx)
        rwa [inv_div] at h0
      have h2 : |u - x| = u - x := abs_of_nonneg (by linarith)
      rw [h2] at h
      have h3 : g / (2 * u) ≤ 1 - x / u := by
        rw [div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div, mul_div_assoc]
        have h4 : x * (2 * u) / u = 2 * x := by field_simp
        rw [mul_div_assoc] at h4
        nlinarith
      exact h3.trans (h1.trans (le_abs_self _))
    · have h1 : 1 - u / x ≤ Real.log (x / u) := by
        have h0 := Real.one_sub_inv_le_log_of_pos (div_pos hx hu)
        rwa [inv_div] at h0
      have e : |Real.log (u / x)| = Real.log (x / u) := by
        rw [Real.log_div hu.ne' hx.ne', Real.log_div hx.ne' hu.ne', abs_sub_comm,
          abs_of_nonneg (by linarith [Real.log_le_log hu hxu.le])]
      rw [e]
      have h2 : |u - x| = x - u := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      rw [h2] at h
      have h3 : g / (2 * u) ≤ 1 - u / x := by
        rw [div_le_iff₀ (by positivity)]
        have h4 : (1 - u / x) * (2 * u) = 2 * u - 2 * u * u / x := by ring
        rw [h4]
        have h5 : u * u / x ≤ u * u / u := div_le_div_of_nonneg_left (by positivity) hu hxu.le
        have h6 : u * u / u = u := by field_simp
        have h7 : 2 * u * u / x = 2 * (u * u / x) := by ring
        rw [h7]
        have h8 : (x - u) ≤ 2 * u - 2 * (u * u / x) := by
          have h9 : u * u / x ≤ u - (x - u) / 2 := by
            rw [div_le_iff₀ hx]
            nlinarith
          linarith
        linarith
      exact h3.trans h1
  unfold kb
  split_ifs with hk
  · rw [div_div, le_div_iff₀ (by positivity)]
    have hTg : T * (g / (2 * u)) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hlog hT.le) hk
    rw [mul_div_assoc'] at hTg
    rw [div_le_one (by positivity)] at hTg
    nlinarith
  · push_neg at hk
    rw [div_div, one_div_le (by positivity) (by positivity), one_div_div]
    have hTg : T * (g / (2 * u)) ≤ T * |Real.log (u / x)| := mul_le_mul_of_nonneg_left hlog hT.le
    have e : T * g / (4 * u) ≤ T * (g / (2 * u)) := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hT.le
      exact div_le_div_of_nonneg_left hg.le (by positivity) (by linarith)
    linarith

theorem kb_le_nearB {u T : ℝ} (hu : 0 < u) (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    (hn2 : (n : ℝ) < 2 * u) : kb T (u / n) ≤ nearB u T n := by
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have f1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu.le
  have f2 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
  unfold nearB
  split_ifs with h1 h2
  · have h3 : (n : ℝ) < ⌊u⌋₊ := by exact_mod_cast h1
    apply kb_le_div hu hT hx hn2 (by linarith)
    refine le_trans ?_ (le_abs_self _)
    linarith
  · exact kb_le_two hT _
  · have h3 : ((⌊u⌋₊ : ℝ) + 1) < n := by exact_mod_cast not_le.mp h2
    apply kb_le_div hu hT hx hn2 (by linarith)
    refine le_trans ?_ (neg_le_abs _)
    linarith

def pTerm (u T : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n)

theorem pTerm_nonneg {u T : ℝ} (hu : 0 < u) (hT : 0 < T) (n : ℕ) : 0 ≤ pTerm u T n := by
  unfold pTerm
  have hk : 0 ≤ kb T (u / n) := by
    unfold kb
    split_ifs with h
    · norm_num
    · push_neg at h
      exact (one_div_pos.mpr (by linarith)).le
  exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)) hk

theorem pTerm_le_far {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n) :
    pTerm u T n ≤ (4 * Real.exp 1 * u / T) * logTerm (cLine u) n := by
  have hu0 : 0 < u := by linarith
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : kb T (u / n) ≤ 4 / T := by
    have := kb_le_of_le hT (by norm_num : (0 : ℝ) < 1 / 2)
      (le_trans (by linarith [Real.log_two_gt_d9]) (abs_log_div_ge_far hu0 hx h))
    refine this.trans (le_of_eq ?_)
    field_simp
    norm_num
  have h2 : (u / n) ^ cLine u = Real.exp 1 * u * (n : ℝ) ^ (-cLine u) := by
    rw [Real.div_rpow hu0.le hx.le, Real.rpow_neg hx.le, rpow_cLine hu]
    rfl
  have h3 : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have h4 : 0 ≤ (u / n) ^ cLine u := Real.rpow_nonneg (by positivity) _
  have h5 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  unfold pTerm logTerm
  calc ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n)
      ≤ Real.log n * (u / n) ^ cLine u * (4 / T) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h3 h4) h1 (kb_nonneg hT _) (mul_nonneg h5 h4)
    _ = (4 * Real.exp 1 * u / T) * (Real.log n * (n : ℝ) ^ (-cLine u)) := by
        rw [h2]; ring

theorem pTerm_le_near {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) {n : ℕ}
    (h1 : u / 2 < (n : ℝ)) (h2 : (n : ℝ) < 2 * u) :
    pTerm u T n ≤ 16 * Real.log u * nearB u T n := by
  have hu0 : 0 < u := by linarith
  have hx : (0 : ℝ) < n := by linarith
  have hn : 0 < n := by exact_mod_cast hx
  have hL := log_ge_half hu
  have a1 : ArithmeticFunction.vonMangoldt n ≤ 2 * Real.log u := by
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    have : Real.log n ≤ Real.log (2 * u) := Real.log_le_log hx h2.le
    rw [Real.log_mul (by norm_num) hu0.ne'] at this
    have h3 : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
    linarith
  have a2 : (u / n) ^ cLine u ≤ 8 := by
    have hle : u / n ≤ 2 := by rw [div_le_iff₀ hx]; linarith
    calc (u / n) ^ cLine u ≤ (2 : ℝ) ^ cLine u :=
          Real.rpow_le_rpow (by positivity) hle (cLine_pos hu).le
      _ ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (cLine_le_three hu)
      _ = 8 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have a3 := kb_le_nearB hu0 hT hn h2
  have b1 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have b2 : 0 ≤ (u / n) ^ cLine u := Real.rpow_nonneg (by positivity) _
  unfold pTerm
  calc ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n)
      ≤ (2 * Real.log u * 8) * nearB u T n :=
        mul_le_mul (mul_le_mul a1 a2 b2 (by linarith)) a3 (kb_nonneg hT _) (by positivity)
    _ = 16 * Real.log u * nearB u T n := by ring

theorem pTerm_le {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) (n : ℕ) :
    pTerm u T n ≤ (4 * Real.exp 1 * u / T) * logTerm (cLine u) n +
      16 * Real.log u * (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) := by
  have hu0 : 0 < u := by linarith
  have hL := log_ge_half hu
  have hA : 0 ≤ (4 * Real.exp 1 * u / T) * logTerm (cLine u) n :=
    mul_nonneg (by positivity) (logTerm_nonneg _ n)
  have hB : 0 ≤ 16 * Real.log u * (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) := by
    apply mul_nonneg (by linarith)
    split_ifs
    · exact nearB_nonneg hu0 hT n
    · exact le_refl _
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · have : pTerm u T n = 0 := by simp [pTerm, h0]
    rw [this]
    linarith
  by_cases hfar : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n
  · have := pTerm_le_far hu hT hn hfar
    linarith
  · rw [not_or, not_le, not_le] at hfar
    have h := pTerm_le_near hu hT hfar.1 hfar.2
    have f2 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
    have hlt : n < ⌊u⌋₊ + (⌊u⌋₊ + 2) := by
      have : (n : ℝ) < ((⌊u⌋₊ + (⌊u⌋₊ + 2) : ℕ) : ℝ) := by push_cast; linarith [hfar.2]
      exact_mod_cast this
    rw [if_pos hlt]
    linarith

theorem sum_pTerm_le {u T : ℝ} (hu : 2 ≤ u) (hT : 2 ≤ T) (K : ℕ) :
    ∑ n ∈ range K, pTerm u T n ≤ 500 * (u * Real.log u ^ 2 / T + Real.log u) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hL := log_ge_half hu
  set L := Real.log u with hLdef
  have h1 : ∑ n ∈ range K, pTerm u T n ≤ (4 * Real.exp 1 * u / T) * ∑ n ∈ range K, logTerm (cLine u) n +
      16 * L * ∑ n ∈ range K, (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun n _ => pTerm_le hu hT0 n)
  have hc : cLine u = 1 + 2 * (1 / (2 * L)) := by
    unfold cLine
    rw [← hLdef]
    field_simp
  have h2 : ∑ n ∈ range K, logTerm (cLine u) n ≤ 4 * L ^ 2 := by
    rw [hc]
    refine (sum_logTerm_le (by positivity) K).trans (le_of_eq ?_)
    field_simp
    norm_num
  have h3 : ∑ n ∈ range K, (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) ≤
      4 + 2 * ((4 * u / T) * (3 * L)) := by
    rw [← Finset.sum_filter]
    have hsub : (range K).filter (fun n => n < ⌊u⌋₊ + (⌊u⌋₊ + 2)) ⊆ range (⌊u⌋₊ + (⌊u⌋₊ + 2)) := by
      intro n hn
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => nearB_nonneg hu0 hT0 n)).trans ?_
    rw [sum_nearB]
    have h4 := sum_inv_le ⌊u⌋₊
    have h5 : Real.log (⌊u⌋₊ : ℝ) ≤ L := by
      apply Real.log_le_log
      · exact_mod_cast Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ u)
      · exact Nat.floor_le hu0.le
    have h6 : ∑ j ∈ range ⌊u⌋₊, 1 / ((j : ℝ) + 1) ≤ 3 * L := by linarith
    have h7 : (4 * u / T) * ∑ j ∈ range ⌊u⌋₊, 1 / ((j : ℝ) + 1) ≤ (4 * u / T) * (3 * L) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    linarith
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have huT : 0 < u / T := by positivity
  have k1 : (4 * Real.exp 1 * u / T) * ∑ n ∈ range K, logTerm (cLine u) n ≤
      (4 * 3 * (u / T)) * (4 * L ^ 2) := by
    have q1 : 4 * Real.exp 1 * u / T ≤ 4 * 3 * (u / T) := by
      have : 4 * Real.exp 1 * u / T = 4 * Real.exp 1 * (u / T) := by ring
      rw [this]
      nlinarith
    exact mul_le_mul q1 h2 (Finset.sum_nonneg (fun n _ => logTerm_nonneg _ n)) (by positivity)
  have k2 : 16 * L * ∑ n ∈ range K, (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) ≤
      16 * L * (4 + 2 * ((4 * u / T) * (3 * L))) := mul_le_mul_of_nonneg_left h3 (by linarith)
  have k3 : u * L ^ 2 / T = (u / T) * L ^ 2 := by ring
  have k4 : 4 * u / T = 4 * (u / T) := by ring
  rw [k3]
  rw [k4] at k2
  have k5 : 0 ≤ (u / T) * L ^ 2 := by positivity
  nlinarith

theorem perronSumBound : PerronSumBound 500 := by
  intro u T hu hT
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  exact ⟨summable_of_sum_range_le (fun n => pTerm_nonneg hu0 hT0 n) (sum_pTerm_le hu hT),
    Real.tsum_le_of_sum_range_le (fun n => pTerm_nonneg hu0 hT0 n) (sum_pTerm_le hu hT)⟩

end PI.EF
