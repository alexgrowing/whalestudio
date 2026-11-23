import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LocalParametrisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def LocalParametrisation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w →
    ∀ U ∈ 𝓝 w, ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ))
      (δ : (Fin d → ℂ) → ℂ) (N : ℕ), B ⊆ U ∧ IsLocalParametrisation X w B A D δ N

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
