import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteCountOfDepth
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_count_of_depth : GlobalTheory.FunPr.Hypotheses₂ → DepthK → InfCountK := by
  first | exact @GlobalTheory.SumCount.infCountK | exact GlobalTheory.SumCount.infCountK | (intros; apply GlobalTheory.SumCount.infCountK <;> assumption)
