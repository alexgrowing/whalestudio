import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDataBound
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_data_bound : GlobalTheory.FunPr.Hypotheses₂ → FinDatK := by
  first | exact @GlobalTheory.FunDat.finDatK | exact GlobalTheory.FunDat.finDatK | (intros; apply GlobalTheory.FunDat.finDatK <;> assumption)
