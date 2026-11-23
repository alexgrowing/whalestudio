import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

def ProperHolomorphicSurjective.Statement : Prop :=
  ∀ (k : ℕ) (Ω D : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen Ω → Ω.Nonempty → IsOpen D → IsPreconnected D → DifferentiableOn ℂ g Ω → Set.MapsTo g Ω D →
    (∀ L ⊆ D, IsCompact L → IsCompact (Ω ∩ g ⁻¹' L)) →
    g '' Ω = D

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
