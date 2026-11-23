import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HolomorphicBoundOfWeightedL2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_bound_of_weighted_L2 : ∀ (n : ℕ) (g : V n → ℂ) (ρ b : ℝ), 0 < ρ → 0 ≤ b → DifferentiableOn ℂ g (Metric.ball 0 ρ) → ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖g z‖ ^ 2 * (‖z‖ ^ 2) ^ (-(b + (n : ℝ)))) < ⊤ → ∃ C ε : ℝ, 0 < ε ∧ ∀ z : V n, z ≠ 0 → ‖z‖ < ε → ‖g z‖ ≤ C * ‖z‖ ^ b := by
  first | exact @GlobalTheory.norm_le_rpow_of_weighted_sq_integrable | exact GlobalTheory.norm_le_rpow_of_weighted_sq_integrable | (intros; apply GlobalTheory.norm_le_rpow_of_weighted_sq_integrable <;> assumption)
