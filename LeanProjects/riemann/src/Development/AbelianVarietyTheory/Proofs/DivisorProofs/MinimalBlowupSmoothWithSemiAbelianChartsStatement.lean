import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalBlowupSmoothWithSemiAbelianCharts
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimalBlowup_smooth_with_semiAbelianCharts : GlobalTheory.SiegJoin.ChartSt5 := by
  first | exact @GlobalTheory.SiegJoin.chartSt5_holds | exact GlobalTheory.SiegJoin.chartSt5_holds | (intros; apply GlobalTheory.SiegJoin.chartSt5_holds <;> assumption)
