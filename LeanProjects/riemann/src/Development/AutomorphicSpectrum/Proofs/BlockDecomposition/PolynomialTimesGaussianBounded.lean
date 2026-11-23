import Mathlib

namespace GlobalTheory.CompanionTheory.EisTube

theorem norm_sq_le_sum_sq (ι : Type) [Fintype ι] (y : ι → ℝ) :
    ‖y‖ ^ 2 ≤ ∑ i, y i ^ 2 := by
  have hs : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hn : ‖y‖ ≤ Real.sqrt (∑ i, y i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun i => y i ^ 2)
      (fun i _ => sq_nonneg (y i)) (Finset.mem_univ i)
  calc ‖y‖ ^ 2 ≤ Real.sqrt (∑ i, y i ^ 2) ^ 2 := by gcongr
    _ = ∑ i, y i ^ 2 := Real.sq_sqrt hs

theorem polyGaussBdd : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c → ∀ N : ℕ, ∃ M : ℝ, ∀ y : ι → ℝ,
    (1 + ‖y‖) ^ N * Real.exp (-(c * ∑ i, y i ^ 2)) ≤ M := by
  intro ι _ c hc N
  refine ⟨2 ^ N * (N.factorial / c ^ N) * Real.exp c, fun y => ?_⟩
  set r : ℝ := ‖y‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg y
  have hS : r ^ 2 ≤ ∑ i, y i ^ 2 := norm_sq_le_sum_sq ι y
  have hcN : 0 < c ^ N := pow_pos hc N

  have h1 : 1 + r ≤ 2 * (1 + r ^ 2) := by nlinarith [sq_nonneg (r - 1)]
  have h2 : (1 + r) ^ N ≤ 2 ^ N * (1 + r ^ 2) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 N

  have h3 : (1 + r ^ 2) ^ N ≤ N.factorial / c ^ N * Real.exp (c * (1 + r ^ 2)) := by
    have h := Real.pow_div_factorial_le_exp (c * (1 + r ^ 2)) (by positivity) N
    have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    rw [div_le_iff₀ hf, mul_pow] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ hcN]
    nlinarith [h]
  have h4 : Real.exp (-(c * ∑ i, y i ^ 2)) ≤ Real.exp (-(c * r ^ 2)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hS hc.le
    linarith
  have h5 : Real.exp (c * (1 + r ^ 2)) * Real.exp (-(c * r ^ 2)) = Real.exp c := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (1 + r) ^ N * Real.exp (-(c * ∑ i, y i ^ 2))
      ≤ (2 ^ N * (N.factorial / c ^ N * Real.exp (c * (1 + r ^ 2)))) *
          Real.exp (-(c * r ^ 2)) := by
        refine mul_le_mul ?_ h4 (Real.exp_pos _).le (by positivity)
        exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = 2 ^ N * (N.factorial / c ^ N) *
          (Real.exp (c * (1 + r ^ 2)) * Real.exp (-(c * r ^ 2))) := by ring
    _ = 2 ^ N * (N.factorial / c ^ N) * Real.exp c := by rw [h5]

end GlobalTheory.CompanionTheory.EisTube
