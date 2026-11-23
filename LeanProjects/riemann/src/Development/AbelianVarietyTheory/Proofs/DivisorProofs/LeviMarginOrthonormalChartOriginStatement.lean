import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMarginOrthonormalChartOrigin
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
theorem _root_.GlobalTheory.T.leviMargin_orthonormal_chart_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (g bb : ℝ), 0 < X.p0 → X.p0 < r → IsOrth X x → 0 ≤ g → 0 ≤ bb → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a) → ∀ ξ : Fin (nd X) → ℂ, (g - bb - 2 * r) * ∑ j, ‖ξ j‖ ^ 2 ≤ leviM X (phla X la) x 0 ξ - bb * leviM X (phla X (GlobalTheory.CurvMargin.blockWt X)) x 0 ξ - leviM X (phla X (kapW X)) x 0 ξ := by
  first | exact @GlobalTheory.LeviOriginMargin.levi_margin_origin | exact GlobalTheory.LeviOriginMargin.levi_margin_origin | (intros; apply GlobalTheory.LeviOriginMargin.levi_margin_origin <;> assumption)
