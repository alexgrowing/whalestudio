import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOfSumBound
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_of_sum_bound : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → DepthK := by
  first | exact @GlobalTheory.DepthUnf.depthK_of_sumOKK₂ | exact GlobalTheory.DepthUnf.depthK_of_sumOKK₂ | (intros; apply GlobalTheory.DepthUnf.depthK_of_sumOKK₂ <;> assumption)
