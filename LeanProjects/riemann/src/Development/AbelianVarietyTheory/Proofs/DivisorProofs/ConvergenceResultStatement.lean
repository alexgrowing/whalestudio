import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvergenceResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_result : ConvSt := by
  first | exact @GlobalTheory.HalfGeo.convSt | exact GlobalTheory.HalfGeo.convSt | (intros; apply GlobalTheory.HalfGeo.convSt <;> assumption)
