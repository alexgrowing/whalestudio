import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteSymmetricMulDifference
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open MvPolynomial GlobalTheory.LineForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_symmetric_mul_difference : ∀ k : ℕ, aeval ![X 0 + X 1, X 0 * X 1] (hs k) * (X 0 - X 1) = (X 0 ^ (k + 1) - X 1 ^ (k + 1) : MvPolynomial (Fin 2) ℝ) := by
  first | exact @GlobalTheory.LineForm.aeval_hs_mul_sub | exact GlobalTheory.LineForm.aeval_hs_mul_sub | (intros; apply GlobalTheory.LineForm.aeval_hs_mul_sub <;> assumption)
