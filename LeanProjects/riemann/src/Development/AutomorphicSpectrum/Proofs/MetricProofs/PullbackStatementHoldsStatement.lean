import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHolds
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_statement_holds : PullbackStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement | exact GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement <;> assumption)
