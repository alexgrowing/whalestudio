import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CumulantLowerBoundOfBoundedCentred
open Matrix Finset Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_le_log_sum_exp_of_bounded_centred : ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (R : ℝ), 0 < R → (∀ J, 0 ≤ w J) → ∑ J, w J = 1 → ∑ J, w J * y J = 0 → (∀ J, w J ≠ 0 → |y J| ≤ R) → min 1 (1 / R) * (∑ J, w J * y J ^ 2) / 4 ≤ Real.log (∑ J, w J * Real.exp (y J)) := by
  first | exact @GlobalTheory.cumulant_lower_bound_of_bounded_centred | exact GlobalTheory.cumulant_lower_bound_of_bounded_centred | (intros; apply GlobalTheory.cumulant_lower_bound_of_bounded_centred <;> assumption)
