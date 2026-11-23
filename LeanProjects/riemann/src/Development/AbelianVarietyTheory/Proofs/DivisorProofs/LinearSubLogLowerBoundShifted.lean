import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace GlobalTheory

theorem linear_sub_log_lower_bound_shifted :
    ∀ C s x : ℝ, 1 ≤ C → 0 < s → s ≤ 1 → -2 - C < x →
      -(C + 2) * Real.log ((C + 2) / s) - (C + 2) ≤ s * x - C * Real.log (2 + C + x) := by
  intro C s x hC hs hs1 hx
  have hy : 0 < 2 + C + x := by linarith
  have hC0 : 0 < C := by linarith
  have hC2 : 0 < C + 2 := by linarith
  have h1 : Real.log ((2 + C + x) * s / C) ≤ (2 + C + x) * s / C - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) hC0.ne', Real.log_mul hy.ne' hs.ne'] at h1
  have h2 : C * (Real.log (2 + C + x) + Real.log s - Real.log C) ≤ (2 + C + x) * s - C := by
    have := mul_le_mul_of_nonneg_left h1 hC0.le
    have e : C * ((2 + C + x) * s / C - 1) = (2 + C + x) * s - C := by field_simp
    linarith
  rw [Real.log_div hC2.ne' hs.ne']
  have h3 : Real.log C ≤ Real.log (C + 2) := Real.log_le_log hC0 (by linarith)
  have h4 : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  have h5 : 0 ≤ Real.log (C + 2) := Real.log_nonneg (by linarith)
  have h6 : C * Real.log C ≤ C * Real.log (C + 2) := mul_le_mul_of_nonneg_left h3 hC0.le
  have h7 : (C + 2) * s ≤ C + 2 := by nlinarith
  nlinarith

end GlobalTheory
