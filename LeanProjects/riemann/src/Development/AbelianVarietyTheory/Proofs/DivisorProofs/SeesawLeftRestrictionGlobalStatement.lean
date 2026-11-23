import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_bound_tuple : GlobalTheory.BigOn.Exp.TupLe.PlacesSt := by
  first | exact @GlobalTheory.BigOn.Exp.TupLe.placesSt | exact GlobalTheory.BigOn.Exp.TupLe.placesSt | (intros; apply GlobalTheory.BigOn.Exp.TupLe.placesSt <;> assumption)
