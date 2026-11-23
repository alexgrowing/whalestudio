import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermProjectionImageNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermRegularDimGe.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N ∈ 𝓝 w, ∀ x ∈ X ∩ N, ∀ (e : ℕ) (A' : (σ → ℂ) →L[ℂ] (Fin e → ℂ)) (O : Set (Fin e → ℂ))
      (V : Set (σ → ℂ)) (g : (Fin e → ℂ) → σ → ℂ),
      IsOpen O → IsOpen V → x ∈ V → AnalyticOnNhd ℂ g O → (∀ y ∈ O, A' (g y) = y) → X ∩ V = g '' O →
        d ≤ e

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
