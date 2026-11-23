import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMLengthParameters
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

def CMRegularElement.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (y : B), y ∈ maximalIdeal B →
    (∀ p ∈ minimalPrimes B, y ∉ p) →
      y ∈ nonZeroDivisors B ∧ IsCohenMacaulayLocalRing (B ⧸ Ideal.span {y})

end GroundTheory.Heights₂.Heights
