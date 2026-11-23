import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists

noncomputable section

namespace PI.EF

open Finset

theorem sum_rpow_le {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε)) ≤ 1 / ε := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(1 + ε))) (Set.Icc 1 (1 + (K : ℝ))) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  beta_reduce at h1
  have h0 : (0 : ℝ) ∉ Set.uIcc 1 (1 + (K : ℝ)) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨fun h => by linarith, h0⟩)] at h1
  have hexp : -(1 + ε) + 1 = -ε := by ring
  rw [hexp, Real.one_rpow] at h1
  have hpos : 0 ≤ (1 + (K : ℝ)) ^ (-ε) := Real.rpow_nonneg (by linarith) _
  have hrhs : ((1 + (K : ℝ)) ^ (-ε) - 1) / (-ε) ≤ 1 / ε := by
    rw [div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  calc ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε))
      = ∑ i ∈ range K, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-(1 + ε)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        push_cast
        ring
    _ ≤ _ := h1
    _ ≤ 1 / ε := hrhs

def logTerm (c : ℝ) (n : ℕ) : ℝ := Real.log n * (n : ℝ) ^ (-c)

theorem logTerm_nonneg (c : ℝ) (n : ℕ) : 0 ≤ logTerm c n := by
  exact mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem sum_logTerm_le {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∑ n ∈ range K, logTerm (1 + 2 * ε) n ≤ 1 / ε ^ 2 := by
  have e0 : logTerm (1 + 2 * ε) 0 = 0 := by simp [logTerm]
  have e1 : logTerm (1 + 2 * ε) 1 = 0 := by simp [logTerm]
  have hb : ∀ i : ℕ, logTerm (1 + 2 * ε) (i + 2) ≤ ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := by
    intro i
    unfold logTerm
    push_cast
    have hx : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have hl := Real.log_le_rpow_div hx.le hε
    have hp : 0 ≤ ((i : ℝ) + 2) ^ (-(1 + 2 * ε)) := Real.rpow_nonneg hx.le _
    calc Real.log ((i : ℝ) + 2) * ((i : ℝ) + 2) ^ (-(1 + 2 * ε))
        ≤ ((i : ℝ) + 2) ^ ε / ε * ((i : ℝ) + 2) ^ (-(1 + 2 * ε)) := mul_le_mul_of_nonneg_right hl hp
      _ = ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hx]
        congr 2
        ring
  calc ∑ n ∈ range K, logTerm (1 + 2 * ε) n
      ≤ ∑ n ∈ range (K + 2), logTerm (1 + 2 * ε) n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun n _ _ => logTerm_nonneg _ n)
    _ = ∑ i ∈ range K, logTerm (1 + 2 * ε) (i + 2) := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [zero_add, e0, e1, add_zero]
    _ ≤ ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := Finset.sum_le_sum fun i _ => hb i
    _ = (∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε))) / ε := (Finset.sum_div _ _ _).symm
    _ ≤ (1 / ε) / ε := div_le_div_of_nonneg_right (sum_rpow_le hε K) hε.le
    _ = 1 / ε ^ 2 := by ring

theorem kb_nonneg {T : ℝ} (hT : 0 < T) (y : ℝ) : 0 ≤ kb T y := by
  unfold kb
  split_ifs
  · norm_num
  · exact div_nonneg zero_le_one (mul_nonneg hT.le (abs_nonneg _))

theorem kb_le_two {T : ℝ} (_hT : 0 < T) (y : ℝ) : kb T y ≤ 2 := by
  unfold kb
  split_ifs with h
  · exact le_rfl
  · have h' := not_le.mp h
    rw [div_le_iff₀ (by linarith)]
    linarith

theorem kb_le_of_le {T d y : ℝ} (hT : 0 < T) (hd : 0 < d) (h : d ≤ |Real.log y|) :
    kb T y ≤ 2 / (T * d) := by
  have hTd : 0 < T * d := mul_pos hT hd
  have hle : T * d ≤ T * |Real.log y| := mul_le_mul_of_nonneg_left h hT.le
  unfold kb
  split_ifs with h1
  · rw [le_div_iff₀ hTd]
    linarith
  · calc 1 / (T * |Real.log y|) ≤ 1 / (T * d) := one_div_le_one_div_of_le hTd hle
      _ ≤ 2 / (T * d) := div_le_div_of_nonneg_right (by norm_num) hTd.le

theorem abs_log_div_ge_far {u x : ℝ} (hu : 0 < u) (hx : 0 < x) (h : x ≤ u / 2 ∨ 2 * u ≤ x) :
    Real.log 2 ≤ |Real.log (u / x)| := by
  rcases h with h | h
  · have h2 : 2 ≤ u / x := by
      rw [le_div_iff₀ hx]
      linarith
    exact (Real.log_le_log (by norm_num) h2).trans (le_abs_self _)
  · have h2 : 2 ≤ x / u := by
      rw [le_div_iff₀ hu]
      linarith
    have hflip : Real.log (u / x) = -Real.log (x / u) := by
      rw [← Real.log_inv, inv_div]
    rw [hflip, abs_neg]
    exact (Real.log_le_log (by norm_num) h2).trans (le_abs_self _)

theorem log_ge_half {u : ℝ} (hu : 2 ≤ u) : 1 / 2 ≤ Real.log u := by
  have h2 := Real.log_le_log (by norm_num) hu
  have h3 := Real.log_two_gt_d9
  linarith

theorem cLine_le_three {u : ℝ} (hu : 2 ≤ u) : cLine u ≤ 3 := by
  have hl := log_ge_half hu
  have h : 1 / Real.log u ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  unfold cLine
  linarith

theorem cLine_pos {u : ℝ} (hu : 2 ≤ u) : 0 < cLine u := by
  have hl := log_ge_half hu
  have h : 0 < 1 / Real.log u := one_div_pos.mpr (by linarith)
  unfold cLine
  linarith

theorem rpow_cLine {u : ℝ} (hu : 2 ≤ u) : u ^ cLine u = Real.exp 1 * u := by
  have hu0 : 0 < u := by linarith
  have hl : Real.log u ≠ 0 := by linarith [log_ge_half hu]
  unfold cLine
  rw [Real.rpow_add hu0, Real.rpow_one, Real.rpow_def_of_pos hu0, mul_one_div_cancel hl, mul_comm]

end PI.EF
