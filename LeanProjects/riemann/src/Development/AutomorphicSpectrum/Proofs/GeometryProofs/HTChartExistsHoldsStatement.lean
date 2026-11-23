import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHolds
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HTChartExists_holds : GlobalTheory.CompanionTheory.Ar.BT.HTChartExists := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists | exact GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists <;> assumption)
