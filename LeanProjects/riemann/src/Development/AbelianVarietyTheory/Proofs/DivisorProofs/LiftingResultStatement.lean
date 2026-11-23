import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifting_result : LiftSt := by
  first | exact @GlobalTheory.HalfGeo.liftSt | exact GlobalTheory.HalfGeo.liftSt | (intros; apply GlobalTheory.HalfGeo.liftSt <;> assumption)
