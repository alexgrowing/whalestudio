import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_result : ChartSt := by
  first | exact @GlobalTheory.HalfGeo.chartSt_holds | exact GlobalTheory.HalfGeo.chartSt_holds | (intros; apply GlobalTheory.HalfGeo.chartSt_holds <;> assumption)
