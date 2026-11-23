import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartSequenceHolds
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_sequence_holds : ChartSequence := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence | exact GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence <;> assumption)
