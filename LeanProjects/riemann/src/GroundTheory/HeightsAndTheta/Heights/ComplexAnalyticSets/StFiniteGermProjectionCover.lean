import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LocalParametrisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteGermProjectionCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N₀ ∈ 𝓝 w, ∀ (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ)),
      IsOpen B → B ⊆ N₀ → w ∈ X ∩ B → IsOpen D → IsPreconnected D → Set.MapsTo A (X ∩ B) D →
      (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
      (∀ x ∈ X ∩ B, A x = A w → x = w) →
      ∃ (δ : (Fin d → ℂ) → ℂ) (N : ℕ), IsLocalParametrisation X w B A D δ N

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
