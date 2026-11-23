import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def LocalMultOrd.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (I W : Ideal A) (x : A)
    [(W.map (Ideal.Quotient.mk I)).IsPrime], W ∈ (I ⊔ Ideal.span {x}).minimalPrimes →
      ((localMult (I ⊔ Ideal.span {x}) W : ℕ) : ℕ∞) =
        Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk I)))
          (algebraMap _ _ (Ideal.Quotient.mk I x))

section Inhabitants

open MvPolynomial

end Inhabitants

end

end GroundTheory.Heights₂.Heights
