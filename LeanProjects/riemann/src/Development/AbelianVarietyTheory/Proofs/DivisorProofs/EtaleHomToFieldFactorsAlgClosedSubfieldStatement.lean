import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomToFieldFactorsAlgClosedSubfield
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_hom_to_field_factors_algClosed_subfield : ∀ (A B K L : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B] [Field K] [IsAlgClosed K] [Field L] (α : A →+* K) (ι : K →+* L) (β : B →+* L), (∀ a ∈ maximalIdeal A, α a = 0) → β.comp (algebraMap A B) = ι.comp α → ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = α ∧ ι.comp ψ = β := by
  first | (exact @GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield) | (exact GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield) | (intros; apply GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield  <;> assumption)
