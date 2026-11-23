import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallExtendByZeroInvariant
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
theorem _root_.GlobalTheory.T.chartBall_extend_by_zero_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (R : ℝ), IsOrth X x → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) → ∀ η : V (nd X) → ℝ, ∃ ψ : Frame X.Ψ r → ℝ, (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) ∧ (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ R ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) ∧ (∀ γ ∈ X.Γ, ∀ y, ψ (lact γ y) = ψ y) ∧ (∀ y, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y) := by
  first | exact @GlobalTheory.chartBall_extend_by_zero | exact GlobalTheory.chartBall_extend_by_zero | (intros; apply GlobalTheory.chartBall_extend_by_zero <;> assumption)
