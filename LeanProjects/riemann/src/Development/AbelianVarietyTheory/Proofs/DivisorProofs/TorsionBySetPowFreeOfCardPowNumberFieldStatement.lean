import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionBySetPowFreeOfCardPowNumberField
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionBySet_pow_free_of_card_pow_numberField : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (w0 : Ideal (𝓞 F)) (h r : ℕ), w0.IsMaximal → w0 ≠ ⊥ → (∀ j : ℕ, Nat.card (Submodule.torsionBySet (𝓞 F) M ((w0 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ (j * h)) → ∃ f : (Fin h → 𝓞 F ⧸ w0 ^ r) →+ M, (∀ (c : 𝓞 F) (a : Fin h → 𝓞 F ⧸ w0 ^ r), f (Ideal.Quotient.mk (w0 ^ r) c • a) = c • f a) ∧ Function.Injective f ∧ ∀ g : M, (∀ c ∈ w0 ^ r, c • g = 0) → ∃ a, f a = g := by
  first | (exact @GlobalTheory.torsionBySet_pow_free_of_natCard) | (exact GlobalTheory.torsionBySet_pow_free_of_natCard) | (intros; apply GlobalTheory.torsionBySet_pow_free_of_natCard  <;> assumption)
