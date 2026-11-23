import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def RegularQuotientIndependent.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsRegularLocalRing S] (h : ℕ) (x : Fin h → S),
    (∀ i, x i ∈ maximalIdeal S) →
    (∀ a : Fin h → S, ∑ i, a i * x i ∈ maximalIdeal S ^ 2 → ∀ i, a i ∈ maximalIdeal S) →
      IsRegularLocalRing (S ⧸ Ideal.span (Set.range x))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
