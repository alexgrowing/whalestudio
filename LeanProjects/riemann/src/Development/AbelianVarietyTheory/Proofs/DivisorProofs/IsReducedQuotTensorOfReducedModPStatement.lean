import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedQuotTensorOfReducedModP
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_quot_tensor_of_reduced_mod_p : ∀ (O : Type) [CommRing O] (k : Type) [Field k] (p : ℕ) (ϖ : O), (p : k) = 0 → IsReduced (k ⊗[ℤ] (O ⧸ Ideal.span {(p : O), ϖ})) → IsReduced ((k ⊗[ℤ] O) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ}) := by
  first | exact @GlobalTheory.reduced_quot_tensor_of_reduced_modp | exact GlobalTheory.reduced_quot_tensor_of_reduced_modp | (intros; apply GlobalTheory.reduced_quot_tensor_of_reduced_modp <;> assumption)
