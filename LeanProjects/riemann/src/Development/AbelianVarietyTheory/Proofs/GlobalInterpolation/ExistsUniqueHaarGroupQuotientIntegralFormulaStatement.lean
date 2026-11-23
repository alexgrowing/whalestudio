import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarGroupQuotientIntegralFormula
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_haar_group_quotient_integral_formula : NormaliseGroupClause := by
  first | exact @GlobalTheory.normaliseGroupClause_holds | exact GlobalTheory.normaliseGroupClause_holds | (intros; apply GlobalTheory.normaliseGroupClause_holds <;> assumption)
