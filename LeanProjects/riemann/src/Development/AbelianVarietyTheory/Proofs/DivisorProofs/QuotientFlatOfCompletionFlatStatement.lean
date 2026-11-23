import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientFlatOfCompletionFlat
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_flat_of_completion_flat : ∀ (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M],
  Module.Flat (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) M) →
  Module.Flat (A ⧸ Ideal.span {f}) (TensorProduct A (A ⧸ Ideal.span {f}) M) := by
  first | exact @GlobalTheory.flat_quot_of_flat_adicCompletion | exact GlobalTheory.flat_quot_of_flat_adicCompletion | (intros; apply GlobalTheory.flat_quot_of_flat_adicCompletion <;> assumption)
