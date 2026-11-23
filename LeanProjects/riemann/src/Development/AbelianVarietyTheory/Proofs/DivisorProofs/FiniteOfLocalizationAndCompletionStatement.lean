import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfLocalizationAndCompletion
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_localization_and_completion : ∀ (A : Type) [CommRing A] (f : A),
  (∀ (Q : Type) [AddCommGroup Q] [Module A Q], (∀ q : Q, ∃ k : ℕ, f ^ k • q = 0) →
    Subsingleton (TensorProduct A (AdicCompletion (Ideal.span {f}) A) Q) → Subsingleton Q) →
  ∀ (N : Type) [AddCommGroup N] [Module A N],
  Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) N) →
  Module.Finite (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) N) →
  Module.Finite A N := by
  first | exact @GlobalTheory.module_finite_of_localization_of_completion | exact GlobalTheory.module_finite_of_localization_of_completion | (intros; apply GlobalTheory.module_finite_of_localization_of_completion <;> assumption)
