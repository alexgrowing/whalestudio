import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntGeneratorsCardEqOfIsLatticePi
import Mathlib
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_span_generators_of_isLattice_pi : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E Λ → ∃ u : Fin (Module.finrank ℚ E * n) → Fin n → E, (∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range u)) ∧ Submodule.span ℚ (Set.range u) = ⊤ := by
  first | exact @GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi | exact GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi | (intros; apply GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi <;> assumption)
