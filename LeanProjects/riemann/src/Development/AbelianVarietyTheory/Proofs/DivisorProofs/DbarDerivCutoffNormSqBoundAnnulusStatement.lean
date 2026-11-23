import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDerivCutoffNormSqBoundAnnulus
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
theorem _root_.GlobalTheory.T.dbarDeriv_cutoff_normSq_bound_annulus : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) → (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) → ∀ (n : ℕ) (ρ : ℝ), 0 < ρ → ∀ (z : V n) (ξ : Fin n → ℂ), ‖∑ j, wdb n j (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ)) z * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ if ρ / 2 ≤ ‖z‖ ∧ ‖z‖ < ρ then A ^ 2 / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.wdb_cutoff_sq_le | exact GlobalTheory.wdb_cutoff_sq_le | (intros; apply GlobalTheory.wdb_cutoff_sq_le <;> assumption)
