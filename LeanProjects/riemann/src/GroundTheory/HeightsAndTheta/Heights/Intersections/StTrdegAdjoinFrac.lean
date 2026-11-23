import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def TrdegAdjoinFrac.Statement : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ D] (E : Type) [CommRing E] [IsDomain E] [Algebra ℤ E]
    [Algebra (FractionRing D) E] (s : Set E),
    Function.Injective (algebraMap ℤ D) →
    Algebra.trdeg ℤ (Algebra.adjoin ℤ
        (Set.range (fun d : D => algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d)) ∪ s)) =
      Algebra.trdeg ℤ D + Algebra.trdeg (FractionRing D) (Algebra.adjoin (FractionRing D) s)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
