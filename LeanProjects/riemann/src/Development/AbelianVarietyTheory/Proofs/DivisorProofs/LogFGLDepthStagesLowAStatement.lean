import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logFGL_depth_stages_lowA : LowAStatement := by
  first | exact @GlobalTheory.DepthStages.lowA_statement | exact GlobalTheory.DepthStages.lowA_statement | (intros; apply GlobalTheory.DepthStages.lowA_statement <;> assumption)
