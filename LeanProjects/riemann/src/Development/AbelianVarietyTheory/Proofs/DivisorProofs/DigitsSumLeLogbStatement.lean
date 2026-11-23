import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DigitsSumLeLogb
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digits_sum_le_mul_logb : ∀ (p n : ℕ), p.Prime → (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  first | exact @GlobalTheory.digits_sum_le_logb | exact GlobalTheory.digits_sum_le_logb | (intros; apply GlobalTheory.digits_sum_le_logb <;> assumption)
