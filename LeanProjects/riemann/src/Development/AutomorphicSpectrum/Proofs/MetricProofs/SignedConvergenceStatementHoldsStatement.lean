import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHolds
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signed_convergence_statement_holds : ConvergenceSignedStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.SignedConv.convergenceSigned | exact GlobalTheory.CompanionTheory.Ar.Giv.SignedConv.convergenceSigned | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.SignedConv.convergenceSigned <;> assumption)
