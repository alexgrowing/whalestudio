import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformIntegrabilityStatementHolds
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_integrability_statement_holds : UnifIntStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.unifInt_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.unifInt_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.unifInt_holds <;> assumption)
