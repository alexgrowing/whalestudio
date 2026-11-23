import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySideOfTwistStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSideOfTwAdm

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reciprocity_side_of_twAdm : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.RecursiveSide := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.recSide_of_twAdm_alt | exact _root_.GlobalTheory.BigOn.Exp.recSide_of_twAdm_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.recSide_of_twAdm_alt <;> assumption)
end
