import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionGlobalStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesSt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_places_statement : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.placesSt_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.placesSt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.placesSt_alt <;> assumption)
end
