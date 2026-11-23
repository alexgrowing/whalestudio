import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryBoundOfInputs
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_bound_of_inputs : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK := by
  first | exact @GlobalTheory.SumSize.dictK_of_normSum | exact GlobalTheory.SumSize.dictK_of_normSum | (intros; apply GlobalTheory.SumSize.dictK_of_normSum <;> assumption)
