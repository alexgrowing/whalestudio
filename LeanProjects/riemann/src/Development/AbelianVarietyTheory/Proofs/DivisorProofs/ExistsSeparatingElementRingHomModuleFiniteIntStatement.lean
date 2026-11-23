import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingElementRingHomModuleFiniteInt
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_element_ringHom_moduleFinite_int : ∀ (k : Type) [Field k] (C : Type) [CommRing C] [Module.Finite ℤ C] (S : Finset (C →+* k)) (χ₀ : C →+* k), ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  first | (exact @GlobalTheory.ringHom_exists_sep_of_moduleFinite_int) | (exact GlobalTheory.ringHom_exists_sep_of_moduleFinite_int) | (intros; apply GlobalTheory.ringHom_exists_sep_of_moduleFinite_int  <;> assumption)
