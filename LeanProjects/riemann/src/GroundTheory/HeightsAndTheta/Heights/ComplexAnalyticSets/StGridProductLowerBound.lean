import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def GridProductLowerBound.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (N : ℕ) (Z : Set (σ → ℂ)) (z₀ : σ → ℂ),
    Bornology.IsBounded Z → z₀ ∉ closure Z →
    ∃ μ : ℝ, 0 < μ ∧ ∃ U ∈ 𝓝 z₀, ∀ z ∈ U, ∀ s : Finset (σ → ℂ), (↑s : Set (σ → ℂ)) ⊆ Z → s.card ≤ N →
      ∃ u : σ → Fin (N + 1), μ ≤ ‖∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i)‖

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
