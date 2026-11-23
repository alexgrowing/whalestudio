import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjection
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_averaging_projection : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (π : G →* Module.End ℂ V) (L : Subgroup G) (D : Submodule ℂ V), (∀ l ∈ L, ∀ x ∈ D, π l x ∈ D) → (∀ x ∈ D, (Set.range fun l : L => π (l : G) x).Finite) → ∃ P : D →ₗ[ℂ] D, (∀ x : D, (∀ l ∈ L, π l (x : V) = x) → P x = x) ∧ (∀ x : D, ∀ l ∈ L, π l (P x : V) = P x) ∧ ∀ x y : D, ∃ (s : Finset G) (f : G → G), s.Nonempty ∧ (∀ g ∈ s, g ∈ L) ∧ (P x : V) = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g (x : V) ∧ (P y : V) = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g (y : V) ∧ Set.BijOn f (s : Set G) (s : Set G) ∧ ∀ g ∈ s, π g⁻¹ (y : V) = π (f g) (y : V) := by
  first | exact @GlobalTheory.orbitAverage_exists | exact GlobalTheory.orbitAverage_exists | (intros; apply GlobalTheory.orbitAverage_exists <;> assumption)
