import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletionFlatKernelFinite
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_flat_kernel_finite : ∀ (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M],
  Module.Flat A M →
  Module.Projective (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) M) →
  ∀ (n : ℕ) (π : (Fin n → A) →ₗ[A] M), Function.Surjective π →
  Module.Finite (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) (LinearMap.ker π)) := by
  first | exact @GlobalTheory.adicCompletion_tensor_ker_finite | exact GlobalTheory.adicCompletion_tensor_ker_finite | (intros; apply GlobalTheory.adicCompletion_tensor_ker_finite <;> assumption)
