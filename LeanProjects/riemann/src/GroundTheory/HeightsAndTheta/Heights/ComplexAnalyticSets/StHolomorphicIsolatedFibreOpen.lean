import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def HolomorphicIsolatedFibreOpen.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → Fin k → ℂ) (u : Fin k → ℂ),
    IsOpen U → u ∈ U → DifferentiableOn ℂ g U →
    (∃ W ∈ 𝓝 u, ∀ v ∈ W, v ∈ U → g v = g u → v = u) →
    ∀ V ∈ 𝓝 u, g '' V ∈ 𝓝 (g u)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
