import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomDualNumberSndEqZero
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_numberField_dualNumber_snd_eq_zero : ∀ (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] {R : Type} [CommRing R] (φ : F →+* DualNumber R) (a : F), (φ a).snd = 0 := by
  first | exact @GlobalTheory.ringHom_dualNumber_snd_eq_zero | exact GlobalTheory.ringHom_dualNumber_snd_eq_zero | (intros; apply GlobalTheory.ringHom_dualNumber_snd_eq_zero <;> assumption)
