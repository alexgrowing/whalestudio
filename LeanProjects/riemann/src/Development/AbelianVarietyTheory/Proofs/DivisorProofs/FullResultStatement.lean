import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_result : FullSt := by
  first | exact @GlobalTheory.HalfGeo.fullSt | exact GlobalTheory.HalfGeo.fullSt | (intros; apply GlobalTheory.HalfGeo.fullSt <;> assumption)
