import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySphereVolumeProductRatioAndInvBounds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySphereVolumeProduct_ratio_and_inv_bounds : (∀ q j : ℕ, j ≤ q → Real.log (sphV q / sphV (q - j)) ≤ 3.49 * j) ∧ ∀ J : ℕ, 0 < sphV J ∧ (sphV J)⁻¹ ≤ (J : ℝ) ^ (J * (J - 1) / 2) := by
  first | exact @GlobalTheory.sphV_ratio_and_inv_bounds | exact GlobalTheory.sphV_ratio_and_inv_bounds | (intros; apply GlobalTheory.sphV_ratio_and_inv_bounds <;> assumption)
