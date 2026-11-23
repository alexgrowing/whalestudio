import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

def LocalizationAtPrimeQuotient.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A) (T : Submonoid (A ⧸ I)) (P : Ideal (Localization T)) [P.IsPrime]
    (W : Ideal A) [W.IsPrime],
    P.comap ((algebraMap (A ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I)) = W →
      ∃ e : Localization.AtPrime P ≃+* (Localization.AtPrime W ⧸ I.map (algebraMap A (Localization.AtPrime W))),
        ∀ a : A,
          e (algebraMap (Localization T) (Localization.AtPrime P)
              (algebraMap (A ⧸ I) (Localization T) (Ideal.Quotient.mk I a))) =
            Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime W)))
              (algebraMap A (Localization.AtPrime W) a)

end

end GroundTheory.Heights₂.Heights
