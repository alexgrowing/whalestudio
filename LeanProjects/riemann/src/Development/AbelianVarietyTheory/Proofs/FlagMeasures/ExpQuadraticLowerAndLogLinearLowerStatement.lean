import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpQuadraticLowerAndLogLinearLower
open Matrix Finset Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_quadratic_lower_and_log_linear_lower' : (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) := by
  first | exact @GlobalTheory.exp_quadratic_lower_and_log_linear_lower | exact GlobalTheory.exp_quadratic_lower_and_log_linear_lower | (intros; apply GlobalTheory.exp_quadratic_lower_and_log_linear_lower <;> assumption)
