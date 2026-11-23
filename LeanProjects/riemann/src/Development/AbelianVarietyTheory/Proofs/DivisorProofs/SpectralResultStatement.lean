import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpectralResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectral_result : SpecSt := by
  first | exact @GlobalTheory.HalfGeo.SpecProof.specSt | exact GlobalTheory.HalfGeo.SpecProof.specSt | (intros; apply GlobalTheory.HalfGeo.SpecProof.specSt <;> assumption)
