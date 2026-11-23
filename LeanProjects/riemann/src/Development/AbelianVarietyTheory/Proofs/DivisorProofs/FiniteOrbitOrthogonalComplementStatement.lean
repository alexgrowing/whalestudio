import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrbitOrthogonalComplement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_orbit_orthogonal_complement : ∀ {V G : Type} [AddCommGroup V] [Module ℂ V] [Group G] (ρ : G →* Module.End ℂ V)
    (B : V → V → ℂ) (D : Submodule ℂ V),
    (∀ g, ∀ x ∈ D, ρ g x ∈ D) →
    (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, B (x + y) z = B x z + B y z) →
    (∀ c : ℂ, ∀ x ∈ D, ∀ y ∈ D, B (c • x) y = c * B x y) →
    (∀ g, ∀ x ∈ D, ∀ y ∈ D, B (ρ g x) (ρ g y) = B x y) →
    ∀ (K : Subgroup G), ∀ y ∈ D, {x | ∃ k ∈ K, ρ k y = x}.Finite →
    ∃ e ∈ Submodule.span ℂ {x | ∃ k ∈ K, ρ k y = x}, (∀ k ∈ K, ρ k e = e) ∧
      ∀ v ∈ D, (∀ k ∈ K, ρ k v = v) → B e v = B y v := by
  first | exact @GlobalTheory.orbit_average_fixed_same_pairing | exact GlobalTheory.orbit_average_fixed_same_pairing | (intros; apply GlobalTheory.orbit_average_fixed_same_pairing <;> assumption)
