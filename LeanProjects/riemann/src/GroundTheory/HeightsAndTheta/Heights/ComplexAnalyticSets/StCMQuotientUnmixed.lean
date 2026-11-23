import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCMUnmixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

def CMQuotientUnmixed.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (d : ℕ) (x : Fin d → B),
    (∀ i, x i ∈ maximalIdeal B) →
    ringKrullDim (B ⧸ Ideal.span (Set.range x)) + (d : WithBot ℕ∞) = ringKrullDim B →
      ∀ p ∈ associatedPrimes B (B ⧸ Ideal.span (Set.range x)),
        p ∈ (Ideal.span (Set.range x)).minimalPrimes ∧
          ringKrullDim (B ⧸ p) = ringKrullDim (B ⧸ Ideal.span (Set.range x))

end GroundTheory.Heights₂.Heights
