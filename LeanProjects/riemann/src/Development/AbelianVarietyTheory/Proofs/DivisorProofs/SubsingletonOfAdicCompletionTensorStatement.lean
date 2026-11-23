import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfAdicCompletionTensor
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_of_adic_completion_tensor : ∀ (A : Type) [CommRing A] (f : A) (N : Type) [AddCommGroup N] [Module A N],
  (∀ n : N, ∃ k : ℕ, f ^ k • n = 0) →
  Subsingleton (TensorProduct A (AdicCompletion (Ideal.span {f}) A) N) → Subsingleton N := by
  first | exact @GlobalTheory.subsingleton_of_adicCompletion_tensor | exact GlobalTheory.subsingleton_of_adicCompletion_tensor | (intros; apply GlobalTheory.subsingleton_of_adicCompletion_tensor <;> assumption)
