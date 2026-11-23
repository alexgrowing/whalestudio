import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterOfSpectralResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_of_spectral_result : SpecSt → CharSt := by
  first | exact @GlobalTheory.HalfGeo.charSt_of_specSt | exact GlobalTheory.HalfGeo.charSt_of_specSt | (intros; apply GlobalTheory.HalfGeo.charSt_of_specSt <;> assumption)
