import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

def CompactHolomorphicFibreFinite.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ) (y : Fin m → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → IsCompact {v | v ∈ U ∧ f v = y} →
      {v | v ∈ U ∧ f v = y}.Finite

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
