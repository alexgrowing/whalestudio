import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteFormBounds
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_infinite_form_bounds : GlobalTheory.FunPr.Hypotheses₂ → FinFormK ∧ InfFormK := by
  first | exact @GlobalTheory.FormVal.form_fin_inf | exact GlobalTheory.FormVal.form_fin_inf | (intros; apply GlobalTheory.FormVal.form_fin_inf <;> assumption)
