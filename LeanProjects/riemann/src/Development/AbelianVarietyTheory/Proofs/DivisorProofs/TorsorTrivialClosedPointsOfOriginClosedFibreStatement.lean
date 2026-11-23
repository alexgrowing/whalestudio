import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsorTrivialClosedPoints_of_origin_closedFibre : GlobalTheory.LocAcyc.KeyOrigin → GlobalTheory.LocAcyc.KeyClosedPts := by
  first | (exact @GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin) | (exact GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin) | (intros; apply GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin  <;> assumption)
