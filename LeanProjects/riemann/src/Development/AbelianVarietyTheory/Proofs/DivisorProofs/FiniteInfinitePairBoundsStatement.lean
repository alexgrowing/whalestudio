import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePairBounds
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_infinite_pair_bounds : GlobalTheory.FunPr.Hypotheses₂ → FinPairK ∧ InfPairK := by
  first | exact @GlobalTheory.FPair.main | exact GlobalTheory.FPair.main | (intros; apply GlobalTheory.FPair.main <;> assumption)
