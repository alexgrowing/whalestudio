import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteScalarBounds
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_infinite_scalar_bounds : GlobalTheory.FunPr.Hypotheses₂ → FinScalK ∧ InfScalK := by
  first | exact @GlobalTheory.ScalAA.finScal_infScal | exact GlobalTheory.ScalAA.finScal_infScal | (intros; apply GlobalTheory.ScalAA.finScal_infScal <;> assumption)
