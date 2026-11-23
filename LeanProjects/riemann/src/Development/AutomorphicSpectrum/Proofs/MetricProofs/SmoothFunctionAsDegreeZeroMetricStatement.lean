import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetric
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_function_as_degree_zero_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D) (u : R.X → ℝ), R.A.Smooth u → ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ x, Real.log (B.h (R.lift x x)) = u x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth | exact GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth <;> assumption)
