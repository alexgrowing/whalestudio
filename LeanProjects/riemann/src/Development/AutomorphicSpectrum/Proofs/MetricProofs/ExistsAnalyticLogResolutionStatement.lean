import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolution
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_log_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → SmoothGenericFibreM y → Nonempty (AnLogRes (mCoordIdeal y) ⊤ D) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.nonempty_anLogRes_of_smoothGenericFibre | exact GlobalTheory.CompanionTheory.Ar.PB.nonempty_anLogRes_of_smoothGenericFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.nonempty_anLogRes_of_smoothGenericFibre <;> assumption)
