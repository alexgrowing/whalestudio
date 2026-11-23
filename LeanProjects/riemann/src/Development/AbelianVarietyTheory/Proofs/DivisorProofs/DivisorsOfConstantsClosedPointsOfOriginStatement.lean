import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsClosedPointsOfOrigin
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin : GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  first | (exact @GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (exact GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (intros; apply GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin  <;> assumption)
