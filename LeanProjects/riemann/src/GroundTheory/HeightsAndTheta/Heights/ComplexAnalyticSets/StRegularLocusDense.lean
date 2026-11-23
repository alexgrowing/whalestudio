import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RegularLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def RegularLocusDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w →
    ∃ N : Set (σ → ℂ), IsOpen N ∧ w ∈ N ∧
      ∀ B : Set (σ → ℂ), IsOpen B → B ⊆ N → X ∩ B ⊆ closure (regLocus (X ∩ B))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
