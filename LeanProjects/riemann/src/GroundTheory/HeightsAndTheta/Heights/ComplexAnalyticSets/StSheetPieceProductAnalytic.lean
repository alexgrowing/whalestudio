import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LocalParametrisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def SheetPieceProductAnalytic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ)
    (U V : Set (σ → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ),
    IsLocalParametrisation X w B A D δ N → IsOpen U → IsOpen V →
    {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V → {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅ →
    ∃ f : (σ → ℂ) → ℂ, AnalyticOnNhd ℂ f (A ⁻¹' D) ∧
      ∀ z, A z ∈ D → δ (A z) ≠ 0 →
        f z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = A z}, (ℓ z - ℓ x)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
