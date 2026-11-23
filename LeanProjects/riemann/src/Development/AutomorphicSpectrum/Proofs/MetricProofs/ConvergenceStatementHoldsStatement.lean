import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_statement_holds : ConvergenceStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds <;> assumption)
