import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformRestrictionStatementHolds
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_restriction_statement_holds : UnifRestrictStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.unifRestrict | exact GlobalTheory.CompanionTheory.Ar.Giv.unifRestrict | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.unifRestrict <;> assumption)
