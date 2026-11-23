import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleIdempotentEqOneAndCharacterEqWeightAl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_eq_one_and_character_eq_of_isIrreducible : ∀ (L : Type) [Field L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V), ρ.IsIrreducible → (∀ e : Module.End L V, e ≠ 0 → e * e = e → (∀ g, ρ g * e = e * ρ g) → e = 1) ∧ (∀ (lam : G →* Lˣ) (v : V), v ≠ 0 → (∀ g, ρ g v = (lam g : L) • v) → ∀ g, ρ.character g = (lam g : L)) := by
  first | exact @GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight | exact GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight | (intros; apply GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight <;> assumption)
