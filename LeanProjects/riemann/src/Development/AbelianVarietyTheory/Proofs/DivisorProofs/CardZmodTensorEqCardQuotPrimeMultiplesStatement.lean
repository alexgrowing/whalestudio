import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardZmodTensorEqCardQuotPrimeMultiples
import Mathlib
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ), Nat.card (TensorProduct ℤ (ZMod p) M) = Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by
  first | exact @GlobalTheory.card_zmod_tensor_eq_card_quot' | exact GlobalTheory.card_zmod_tensor_eq_card_quot' | (intros; apply GlobalTheory.card_zmod_tensor_eq_card_quot' <;> assumption)
