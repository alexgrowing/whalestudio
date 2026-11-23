import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HolomorphicIsBigOOfHalfPowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_isBigO_of_half_power_bound : ∀ (n a : ℕ) (g : V n → ℂ) (ρ C : ℝ), 0 < n → 0 < ρ → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ z : V n, z ≠ 0 → ‖z‖ < ρ → ‖g z‖ ≤ C * ‖z‖ ^ ((a : ℝ) - 1 / 2)) → g =O[𝓝 0] fun z => ‖z‖ ^ a := by
  first | exact @GlobalTheory.isBigO_norm_pow_of_le_rpow_sub_half_euclidean | exact GlobalTheory.isBigO_norm_pow_of_le_rpow_sub_half_euclidean | (intros; apply GlobalTheory.isBigO_norm_pow_of_le_rpow_sub_half_euclidean <;> assumption)
