import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallWeightPotentialDensityBounds
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartBall_weightPotential_density_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (z : V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → z ∈ OmF X x ∧ |phla X la (cpt X x z)| ≤ ∑ τ, ∑ a, |(la τ a : ℝ)| ∧ |rhF X x z| ≤ (X.Ψ.card : ℝ) ∧ |Real.log (densF X x z)| ≤ (X.Ψ.card : ℝ) * r ∧ 0 < densF X x z := by
  first | exact @GlobalTheory.WeightSizes.chart_ball_sizes | exact GlobalTheory.WeightSizes.chart_ball_sizes | (intros; apply GlobalTheory.WeightSizes.chart_ball_sizes <;> assumption)
