import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricSumBelowThreshold
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_sum_below_threshold : ∀ (q s Y : ℝ), 1 < q → 0 < s → 0 < Y → (∑' n : ℤ, (if q ^ n ≤ Y then ENNReal.ofReal (q ^ (s * (n : ℝ))) else 0)) ≤ ENNReal.ofReal (Y ^ s / (1 - q ^ (-s))) := by
  first | exact @GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div | exact GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div | (intros; apply GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div <;> assumption)
