import Mathlib

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

theorem exists_power_sum_lower_bound (C : ℝ) (a : ℕ) (hC : 0 < C)
    (hT : ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n → (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
      ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + a * n ∧ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i, z i ^ k‖)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (N : ℕ) (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re) (hi : ∃ i, 1 / 2 ≤ ‖u i‖)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ j n : ℕ, m + 1 ≤ j ∧ j ≤ m + a * n ∧ 1 ≤ n ∧ (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re ∧
      (1 / 2) ^ j * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤
        ‖∑ i, u i ^ j‖ + ε ^ (j - 2) * ∑ i, (u i).re := by
  classical
  have hre0 : ∀ i, 0 ≤ (u i).re := fun i => le_trans (sq_nonneg _) (hu i)
  have hle1 : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h1 := hu i
    have h2 : (u i).re ≤ ‖u i‖ := by
      first
        | exact Complex.re_le_norm (u i)
        | exact Complex.re_le_abs (u i)
    nlinarith [norm_nonneg (u i)]
  obtain ⟨i0, hi0⟩ := hi

  set I := Finset.univ.filter (fun i => ε ≤ ‖u i‖) with hIdef
  have hi0I : i0 ∈ I := Finset.mem_filter.2 ⟨Finset.mem_univ _, by linarith⟩
  have hIne : I.Nonempty := ⟨i0, hi0I⟩
  obtain ⟨i1, hi1I, hi1⟩ := Finset.exists_mem_eq_sup' hIne (fun i => ‖u i‖)
  set r := I.sup' hIne (fun i => ‖u i‖) with hr
  have hr0 : 1 / 2 ≤ r := le_trans hi0 (Finset.le_sup' (fun i => ‖u i‖) hi0I)
  have hrpos : 0 < r := by linarith
  have hnr : ‖(r : ℂ)‖ = r := by
    first
      | rw [Complex.norm_real, Real.norm_of_nonneg hrpos.le]
      | simp [abs_of_pos hrpos]
  set n := I.card with hn
  have hn1 : 1 ≤ n := Finset.card_pos.2 hIne
  let e : Fin n ≃ I := I.equivFin.symm
  let z : Fin n → ℂ := fun k => u (e k) / r
  have hz1 : ∀ k, ‖z k‖ ≤ 1 := by
    intro k
    simp only [z]
    rw [norm_div, hnr, div_le_one hrpos]
    exact Finset.le_sup' (fun i => ‖u i‖) (e k).2
  have hz2 : ∃ k, ‖z k‖ = 1 := by
    refine ⟨e.symm ⟨i1, hi1I⟩, ?_⟩
    simp only [z, Equiv.apply_symm_apply]
    rw [norm_div, hnr, ← hi1]
    exact div_self hrpos.ne'
  obtain ⟨k, hk1, hk2, hkB⟩ := hT n m z hn1 hz1 hz2

  have hsumz : ∑ k', z k' ^ k = (∑ i ∈ I, u i ^ k) / (r : ℂ) ^ k := by
    simp only [z, div_pow]
    rw [← Finset.sum_div]
    congr 1
    rw [← Finset.sum_coe_sort I]
    exact e.sum_comp (fun i : I => u i ^ k)
  have hB0 : 0 ≤ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hC.le (by positivity))) _
  have hmain : (1 / 2) ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i ∈ I, u i ^ k‖ := by
    rw [hsumz, norm_div, norm_pow, hnr, le_div_iff₀ (pow_pos hrpos k)] at hkB
    calc (1 / 2) ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n)
        ≤ r ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hr0 k) hB0
      _ ≤ ‖∑ i ∈ I, u i ^ k‖ := by linarith

  have hcompl : ∑ i ∈ Iᶜ, ‖u i‖ ^ k ≤ ε ^ (k - 2) * ∑ i, (u i).re := by
    calc ∑ i ∈ Iᶜ, ‖u i‖ ^ k ≤ ∑ i ∈ Iᶜ, ε ^ (k - 2) * (u i).re := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hlt : ‖u i‖ < ε := by
            rw [Finset.mem_compl, Finset.mem_filter] at hi
            push_neg at hi
            exact hi (Finset.mem_univ _)
          calc ‖u i‖ ^ k = ‖u i‖ ^ 2 * ‖u i‖ ^ (k - 2) := by
                rw [← pow_add]
                congr 1
                omega
            _ ≤ (u i).re * ε ^ (k - 2) :=
                mul_le_mul (hu i) (pow_le_pow_left₀ (norm_nonneg _) hlt.le _) (by positivity) (hre0 i)
            _ = ε ^ (k - 2) * (u i).re := by ring
      _ = ε ^ (k - 2) * ∑ i ∈ Iᶜ, (u i).re := by rw [Finset.mul_sum]
      _ ≤ ε ^ (k - 2) * ∑ i, (u i).re :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hre0 i)
            (by positivity)
  have hsplit : ‖∑ i ∈ I, u i ^ k‖ ≤ ‖∑ i, u i ^ k‖ + ∑ i ∈ Iᶜ, ‖u i‖ ^ k := by
    have h := Finset.sum_add_sum_compl I (fun i => u i ^ k)
    have h' : ∑ i ∈ I, u i ^ k = ∑ i, u i ^ k - ∑ i ∈ Iᶜ, u i ^ k := by
      rw [← h]
      ring
    rw [h']
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_pow _ _))
  have hnε : (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re := by
    calc (n : ℝ) * ε ^ 2 = ∑ i ∈ I, ε ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ I, (u i).re := Finset.sum_le_sum fun i hi =>
          le_trans (pow_le_pow_left₀ hε0.le (Finset.mem_filter.1 hi).2 2) (hu i)
      _ ≤ ∑ i, (u i).re :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hre0 i
  refine ⟨k, n, hk1, hk2, hn1, hnε, ?_⟩
  linarith [hmain, hsplit, hcompl]

theorem turan_lb (C : ℝ) (hC : 0 < C) (a n m : ℕ) (hn : 1 ≤ n) :
    Real.exp (-((a : ℝ) * m) - a * n * Real.log (max C 1)) ≤ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hCm : 0 < max C 1 := lt_max_of_lt_right one_pos
  have h1 : Real.exp (-(m : ℝ) / n) * (m + n) ≤ n :=
    calc Real.exp (-(m : ℝ) / n) * (m + n) = n * (Real.exp (-(m : ℝ) / n) * ((m : ℝ) / n + 1)) := by
          field_simp
      _ ≤ n * (Real.exp (-(m : ℝ) / n) * Real.exp ((m : ℝ) / n)) := by
          gcongr
          exact Real.add_one_le_exp _
      _ = n := by
          rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, mul_one]
  have hb : Real.exp (-(m : ℝ) / n - Real.log (max C 1)) ≤ (n : ℝ) / (C * (m + n)) := by
    rw [Real.exp_sub, Real.exp_log hCm]
    have h2 : Real.exp (-(m : ℝ) / n) ≤ n / (m + n) := by
      rw [le_div_iff₀ (by positivity)]
      exact h1
    calc Real.exp (-(m : ℝ) / n) / max C 1 ≤ ((n : ℝ) / (m + n)) / max C 1 := by gcongr
      _ ≤ ((n : ℝ) / (m + n)) / C := by
          gcongr
          exact le_max_left _ _
      _ = n / (C * (m + n)) := by rw [div_div, mul_comm]
  calc Real.exp (-((a : ℝ) * m) - a * n * Real.log (max C 1))
      = Real.exp (-(m : ℝ) / n - Real.log (max C 1)) ^ (a * n) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp
    _ ≤ ((n : ℝ) / (C * (m + n))) ^ (a * n) := pow_le_pow_left₀ (Real.exp_pos _).le hb _

theorem fact_bound (x : ℝ) (hx : 0 ≤ x) (j : ℕ) (hj : 1 ≤ j) :
    x ^ j / ((j - 1).factorial : ℝ) ≤ j * (Real.exp 1 * x / j) ^ j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hF : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hF1 : ((j - 1).factorial : ℝ) ≠ 0 := by positivity
  have hP : (0 : ℝ) < (j : ℝ) ^ j := pow_pos hjpos j
  have hfact : ((j - 1).factorial : ℝ) * j = j.factorial := by
    have : j * (j - 1).factorial = j.factorial := by
      first
        | exact Nat.mul_factorial_pred (show j ≠ 0 by omega)
        | exact Nat.mul_factorial_pred (show 0 < j by omega)
    rw [← this]
    push_cast
    ring
  have hkey : (j : ℝ) ^ j / j.factorial ≤ Real.exp 1 ^ j :=
    calc (j : ℝ) ^ j / j.factorial ≤ Real.exp j := by
          first
            | exact Real.pow_div_factorial_le_exp _ hjpos.le j
            | exact Real.pow_div_factorial_le_exp hjpos.le j
      _ = Real.exp 1 ^ j := by rw [← Real.exp_nat_mul, mul_one]
  have h1 : 1 / (j.factorial : ℝ) ≤ Real.exp 1 ^ j / (j : ℝ) ^ j := by
    rw [div_le_div_iff₀ hF hP]
    rw [div_le_iff₀ hF] at hkey
    linarith
  have hx' : 0 ≤ (j : ℝ) * x ^ j := by positivity
  calc x ^ j / ((j - 1).factorial : ℝ) = ((j : ℝ) * x ^ j) * (1 / j.factorial) := by
        rw [← hfact]
        field_simp
    _ ≤ ((j : ℝ) * x ^ j) * (Real.exp 1 ^ j / (j : ℝ) ^ j) := mul_le_mul_of_nonneg_left h1 hx'
    _ = j * (Real.exp 1 * x / j) ^ j := by
        rw [div_pow, mul_pow]
        ring

theorem log_sq_bound (M : ℝ) (hM : 1 ≤ M) : Real.log (3 * M) ^ 2 ≤ 32 * Real.sqrt M := by
  have h3M : (1 : ℝ) ≤ 3 * M := by linarith
  have hL0 : 0 ≤ Real.log (3 * M) := Real.log_nonneg h3M
  have hL : Real.log (3 * M) ≤ (3 * M) ^ ((1 : ℝ) / 4) / (1 / 4) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have hq : ((3 * M) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt (3 * M) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : Real.sqrt (3 * M) ≤ 2 * Real.sqrt M := by
    rw [← h4, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log (3 * M) ^ 2 ≤ ((3 * M) ^ ((1 : ℝ) / 4) / (1 / 4)) ^ 2 :=
        pow_le_pow_left₀ hL0 hL 2
    _ = 16 * ((3 * M) ^ ((1 : ℝ) / 4)) ^ 2 := by ring
    _ = 16 * Real.sqrt (3 * M) := by rw [hq]
    _ ≤ 32 * Real.sqrt M := by linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
