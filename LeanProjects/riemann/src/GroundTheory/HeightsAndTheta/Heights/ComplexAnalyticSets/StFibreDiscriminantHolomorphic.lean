import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GenericCountCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FibreDiscriminantHolomorphic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ))
    (N : ℕ) (l : (σ → ℂ) →L[ℂ] ℂ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x)) →
    IsGenericCountCover Y A D N →
    AnalyticOnNhd ℂ (fibreDiscr Y A l N) D

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
