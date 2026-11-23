import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_statement_holds : ChartSt := by
  first | exact @GlobalTheory.FlatModel.chartSt | exact GlobalTheory.FlatModel.chartSt | (intros; apply GlobalTheory.FlatModel.chartSt <;> assumption)
