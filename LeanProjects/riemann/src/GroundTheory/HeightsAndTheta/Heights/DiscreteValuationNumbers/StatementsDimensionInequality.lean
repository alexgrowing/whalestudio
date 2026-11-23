import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

def DimensionInequality.Statement : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.FiniteType A B], Function.Injective (algebraMap A B) →
    ∀ (P : Ideal B) [P.IsPrime],
      Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (B ⧸ P) ≤
        Cardinal.ofENat (P.under A).height + Algebra.trdeg A B

end GroundTheory.Heights₂.Heights.NumbersDVR
