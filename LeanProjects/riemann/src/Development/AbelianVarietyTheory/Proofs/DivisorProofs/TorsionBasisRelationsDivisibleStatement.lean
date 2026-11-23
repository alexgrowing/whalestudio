import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionBasisRelationsDivisible
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_basis_relations_divisible : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    Nat.card {x : M // N • x = 0} = N ^ (2 * Module.finrank ℚ F) →
    ∀ p : Fin 2 → M, (∀ i, N • p i = 0) →
    (∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1) →
    ∀ a b : 𝓞 F, a • p 0 + b • p 1 = 0 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  first | exact @GlobalTheory.dvd_of_two_gens_of_card_torsion | exact GlobalTheory.dvd_of_two_gens_of_card_torsion | (intros; apply GlobalTheory.dvd_of_two_gens_of_card_torsion <;> assumption)
