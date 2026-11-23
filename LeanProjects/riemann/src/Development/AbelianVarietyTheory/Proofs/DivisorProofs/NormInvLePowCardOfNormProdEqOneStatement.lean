import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormInvLePowCardOfNormProdEqOne
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_inv_le_pow_card_of_norm_prod_eq_one' : ∀ (B : Multiset ℂˣ) (M : ℝ), 1 ≤ M → (∀ b ∈ B, ‖(b : ℂ)‖ ≤ M) → ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 → ∀ b ∈ B, ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ M ^ B.card := by
  first | exact @GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one | exact GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one | (intros; apply GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one <;> assumption)
