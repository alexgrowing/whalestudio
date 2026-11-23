import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfEqualAnnihilators
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_graph_of_equal_annihilators : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) (C : ι → Subalgebra ℂ (Module.End ℂ V)) (U₁ U₂ : Submodule ℂ V), FiniteDimensional ℂ U₁ → U₁ ≠ ⊥ → U₂ ≠ ⊥ → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₁, c x ∈ U₁) → (∀ v, ∀ c ∈ C v, ∀ x ∈ U₂, c x ∈ U₂) → (∀ v w, v ≠ w → ∀ c ∈ C v, ∀ d ∈ C w, (∀ x ∈ U₁, c (d x) = d (c x)) ∧ (∀ x ∈ U₂, c (d x) = d (c x))) → (∀ v, ∀ c ∈ C v, (∀ x ∈ U₁, c x = 0) ↔ (∀ x ∈ U₂, c x = 0)) → (∀ Y ≤ U₁, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₁) → (∀ Y ≤ U₂, (∀ v, ∀ c ∈ C v, ∀ x ∈ Y, c x ∈ Y) → Y = ⊥ ∨ Y = U₂) → ∃ X : Submodule ℂ (V × V), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ U₁ ∧ z.2 ∈ U₂) ∧ (∀ v, ∀ c ∈ C v, ∀ z ∈ X, (c z.1, c z.2) ∈ X) ∧ (∀ u, ((0 : V), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : V)) ∈ X → u = 0) := by
  first | exact @GlobalTheory.CommDet.stable_graph | exact GlobalTheory.CommDet.stable_graph | (intros; apply GlobalTheory.CommDet.stable_graph <;> assumption)
