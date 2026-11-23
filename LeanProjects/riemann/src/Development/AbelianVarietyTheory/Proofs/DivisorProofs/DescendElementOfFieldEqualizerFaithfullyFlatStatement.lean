import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendElementOfFieldEqualizerFaithfullyFlat
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descend_element_of_field_equalizer_faithfully_flat : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] [CommRing R₁] [Algebra R R₁], Module.Finite R R₁ → Module.FaithfullyFlat R R₁ → ∀ s : R₁, (∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s) → ∃ e : R, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K), i₁ s = i₁ (algebraMap R R₁ e) := by
  first | exact @GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq | exact GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq | (intros; apply GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq <;> assumption)
