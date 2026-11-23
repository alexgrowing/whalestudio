import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallBoundTupleStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefSt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_coef_le : _root_.GlobalTheory.BigOn.Exp.TupLe.CoefficientCondition' := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.CoefPf.coefSt_alt <;> assumption)
end
