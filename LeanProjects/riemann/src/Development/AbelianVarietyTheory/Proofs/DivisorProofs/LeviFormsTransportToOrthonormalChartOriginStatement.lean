import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormsTransportToOrthonormalChartOrigin
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
theorem _root_.GlobalTheory.T.leviForms_transport_to_orthonormal_chart_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x1 b : Frame X.Ψ r) (z : V (nd X)), IsOrth X x1 → z ∈ OmF X x0 → b ∈ Bor X.Ψ r → cpt X x0 z = rmul x1 b → ∀ ξ : Fin (nd X) → ℂ, ∃ ξ' : Fin (nd X) → ℂ, (∀ la : Wt X.Ψ r, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 ξ') ∧ ∃ B : Frame X.Ψ r, (∀ τ (a c : Fin r), c < a → B τ a c = 0) ∧ ∀ τ, mat x0 τ * (mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) = mat x1 τ * ((mat (nmat X (WithLp.toLp 2 ξ')) τ - 1) * mat b τ + mat B τ) := by
  first | exact @GlobalTheory.LeviWeightChart.levi_transport_origin | exact GlobalTheory.LeviWeightChart.levi_transport_origin | (intros; apply GlobalTheory.LeviWeightChart.levi_transport_origin <;> assumption)
