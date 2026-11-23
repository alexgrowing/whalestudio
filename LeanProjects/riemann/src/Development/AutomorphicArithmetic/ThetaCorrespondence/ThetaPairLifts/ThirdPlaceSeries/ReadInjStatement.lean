import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadInjectiveStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeHasSmallGenerators
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadInj

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.read_injective : _root_.GlobalTheory.BigOn.Exp.ReadInjAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.readInj_alt | exact _root_.GlobalTheory.BigOn.Exp.readInj_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.readInj_alt <;> assumption)
end
