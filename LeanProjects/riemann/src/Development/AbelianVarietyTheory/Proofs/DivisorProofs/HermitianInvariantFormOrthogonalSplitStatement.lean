import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianInvariantFormOrthogonalSplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_invariant_form_orthogonal_split : ∀ {V G : Type} [AddCommGroup V] [Module ℂ V] [Group G] (ρ : G →* Module.End ℂ V)
    (B : V → V → ℂ) (D : Submodule ℂ V),
    (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x + y) z = B x z + B y z) →
    (∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B (c • x) y = c * B x y) →
    (∀ x ∈ D, ∀ y ∈ D, B y x = starRingEnd ℂ (B x y)) →
    (∀ g, ∀ x ∈ D, ∀ y ∈ D, B (ρ g x) (ρ g y) = B x y) →
    (∀ x ∈ D, B x x = 0 → ∀ y ∈ D, B y x = 0) →
    ∀ (U : Submodule ℂ V), U ≤ D → ∀ (K₀ : Subgroup G) (P : Submodule ℂ V), P ≤ U →
    (∀ g, ∀ x ∈ P, ρ g x ∈ P) →
    (∀ Z : Submodule ℂ V, Z ≤ U → (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) →
      ∀ u ∈ U, ∃ z ∈ Z, ∀ y ∈ Z, B y (u - z) = 0) →
    (∀ Z : Submodule ℂ V, Z ≤ U → (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) → (∃ z ∈ Z, B z z ≠ 0) →
      ∃ a ∈ Z, (∀ k ∈ K₀, ρ k a = a) ∧ B a a ≠ 0) →
    (∃ s : Finset V, (↑s ⊆ (D : Set V)) ∧ ∀ y ∈ U, (∀ k ∈ K₀, ρ k y = y) →
      ∃ z ∈ Submodule.span ℂ (s : Set V), B (y - z) (y - z) = 0) →
    (∃ z ∈ P, B z z ≠ 0) →
    ∃ Z : Submodule ℂ V, Z ≤ P ∧ (∀ g, ∀ x ∈ Z, ρ g x ∈ Z) ∧ (∃ z ∈ Z, B z z ≠ 0) ∧
      ∀ Z₁ : Submodule ℂ V, Z₁ ≤ Z → (∀ g, ∀ x ∈ Z₁, ρ g x ∈ Z₁) →
        (∀ z ∈ Z₁, B z z = 0) ∨ ∀ z ∈ Z, ∃ z₁ ∈ Z₁, B (z - z₁) (z - z₁) = 0 := by
  first | exact @GlobalTheory.StableMinFix.exists_minimal_simple_mod_radical | exact GlobalTheory.StableMinFix.exists_minimal_simple_mod_radical | (intros; apply GlobalTheory.StableMinFix.exists_minimal_simple_mod_radical <;> assumption)
