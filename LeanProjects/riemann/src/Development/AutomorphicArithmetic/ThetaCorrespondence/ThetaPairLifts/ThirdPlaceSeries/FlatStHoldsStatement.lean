import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceBoundTupleStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatStHolds

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_flat_estimate : _root_.GlobalTheory.BigOn.Exp.TupLe.FlatCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.flatSt_holds_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.flatSt_holds_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.flatSt_holds_alt <;> assumption)
end
