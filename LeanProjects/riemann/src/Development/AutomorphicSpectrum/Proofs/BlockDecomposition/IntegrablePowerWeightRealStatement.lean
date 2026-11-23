import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightReal
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_power_weight_real : ∀ (r N : ℝ), -1 < r → r + 1 < N → MeasureTheory.Integrable (fun x : ℝ => |x| ^ r * (1 + |x|) ^ (-N)) := by
  first | exact @GlobalTheory.CompanionTheory.RealTateConv.integrable_abs_rpow_mul_one_add_abs_rpow | exact GlobalTheory.CompanionTheory.RealTateConv.integrable_abs_rpow_mul_one_add_abs_rpow | (intros; apply GlobalTheory.CompanionTheory.RealTateConv.integrable_abs_rpow_mul_one_add_abs_rpow <;> assumption)
