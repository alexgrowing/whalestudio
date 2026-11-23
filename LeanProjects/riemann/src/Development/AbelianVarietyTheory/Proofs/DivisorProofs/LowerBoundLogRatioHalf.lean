import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSubLogLowerBoundShifted

namespace GlobalTheory

theorem neg_mul_log_div_sq_le_of_linear_sub_log_le :
    ∀ C : ℝ, ∃ C' : ℝ, ∀ B t x h : ℝ, 2 ≤ B → 0 < t → t ≤ 1 / 2 → 0 ≤ x →
      t / 4 * x - C * Real.log (2 + x) - C * Real.log B - C ≤ h →
        -(C' * Real.log (B / t ^ 2)) ≤ h := by
  intro C
  obtain ⟨D, hD1, hCD⟩ : ∃ D : ℝ, 1 ≤ D ∧ C ≤ D := ⟨max C 1, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (D + 2) * (Real.log (D + 2) + Real.log 4 + 1) + D := ⟨_, rfl⟩
  refine ⟨(D + 2) + 2 * M, ?_⟩
  intro B t x h hB ht ht2 hx hh
  have key := linear_sub_log_lower_bound_shifted D (t / 4) x hD1 (by positivity) (by linarith)
    (by linarith)
  have hD2 : 0 < D + 2 := by linarith
  rw [Real.log_div hD2.ne' (by positivity), Real.log_div ht.ne' (by norm_num)] at key
  rw [Real.log_div (by linarith) (by positivity), Real.log_pow]
  have hlt : Real.log t ≤ 0 := Real.log_nonpos ht.le (by linarith)
  have hB2 : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB
  have hl2 := Real.log_two_gt_d9
  have ha : 1 / 2 ≤ Real.log B := by linarith
  have hx0 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  have hx1 : Real.log (2 + x) ≤ Real.log (2 + D + x) := Real.log_le_log (by linarith) (by linarith)
  have h1 : C * Real.log (2 + x) ≤ D * Real.log (2 + D + x) :=
    (mul_le_mul_of_nonneg_right hCD hx0).trans (mul_le_mul_of_nonneg_left hx1 (by linarith))
  have h2 : C * Real.log B ≤ D * Real.log B := mul_le_mul_of_nonneg_right hCD (by linarith)
  have hM0 : 0 ≤ M := by
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h5 : 0 ≤ Real.log (D + 2) := Real.log_nonneg (by linarith)
    rw [hM]; positivity
  have h3 : 0 ≤ M * (Real.log B - 1 / 2) := mul_nonneg hM0 (by linarith)
  have h6 : 0 ≤ M * (-Real.log t) := mul_nonneg hM0 (by linarith)
  have h7 : 0 ≤ (D + 2) * (-Real.log t) := mul_nonneg hD2.le (by linarith)
  have h8 : -M + (D + 2) * Real.log t - D * Real.log B ≤ h := by
    rw [hM]; nlinarith
  push_cast
  nlinarith

end GlobalTheory
