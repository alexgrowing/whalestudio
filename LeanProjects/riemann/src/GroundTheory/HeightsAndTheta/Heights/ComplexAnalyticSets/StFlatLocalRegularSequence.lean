import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatDimFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

def FlatLocalRegularSequence.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) → Module.Flat A B →
      ∀ (rs : List A) (ys : List B), (∀ r ∈ rs, r ∈ maximalIdeal A) → IsWeaklyRegular A rs →
        (∀ y ∈ ys, y ∈ maximalIdeal B) →
        IsWeaklyRegular (B ⧸ (maximalIdeal A).map (algebraMap A B))
          (ys.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))) →
        IsWeaklyRegular B (rs.map (algebraMap A B) ++ ys)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
