import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteClassBound
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_class_bound : GlobalTheory.FunPr.Hypotheses₂ → InfClassK := by
  first | exact @GlobalTheory.ClassCount.infClassK | exact GlobalTheory.ClassCount.infClassK | (intros; apply GlobalTheory.ClassCount.infClassK <;> assumption)
