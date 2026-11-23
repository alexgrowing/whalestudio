import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowAt : _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt | exact _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt <;> assumption)
end
