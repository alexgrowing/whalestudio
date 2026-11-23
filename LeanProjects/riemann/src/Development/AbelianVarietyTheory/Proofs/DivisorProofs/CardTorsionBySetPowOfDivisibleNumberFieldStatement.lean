import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberField
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsionBySet_pow_of_divisible_numberField : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (w0 : Ideal (𝓞 F)) (h : ℕ), w0.IsMaximal → w0 ≠ ⊥ → (∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g)) → Nat.card (Submodule.torsionBySet (𝓞 F) M (w0 : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ h → ∀ j : ℕ, Nat.card (Submodule.torsionBySet (𝓞 F) M ((w0 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ (j * h) := by
  first | (exact @GlobalTheory.torsion_pow_card) | (exact GlobalTheory.torsion_pow_card) | (intros; apply GlobalTheory.torsion_pow_card  <;> assumption)
