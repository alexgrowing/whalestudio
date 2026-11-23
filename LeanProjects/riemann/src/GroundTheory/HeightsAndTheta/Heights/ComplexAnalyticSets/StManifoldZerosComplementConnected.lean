import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RegularLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ManifoldZerosComplementConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (R : Set (σ → ℂ)) (h : (σ → ℂ) → ℂ),
    IsPreconnected R → (∀ x ∈ R, IsRegularPointOf R x) → (∀ x ∈ R, AnalyticAt ℂ h x) →
    (∃ x ∈ R, h x ≠ 0) → IsPreconnected (R \ {z | h z = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
