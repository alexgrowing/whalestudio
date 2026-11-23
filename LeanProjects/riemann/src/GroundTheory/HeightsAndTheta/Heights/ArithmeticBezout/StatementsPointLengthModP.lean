import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeGeoNum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime)

def PointLengthModP.Statement : Prop :=
  ∀ (n p : ℕ) (W : Ideal (MRing (PBlk n))) (F : Type) [Field F],
    p.Prime → IsMultiProjPrime W → C (p : ℤ) ∈ W →
      Function.Surjective (Int.castRingHom F) → ((p : ℤ) : F) = 0 →
        ∀ i : Fin n,
          (Module.length ℤ (MRing (PBlk n) ⧸ (W ⊔ Ideal.span {(X ⟨(), i⟩ : MRing (PBlk n)) - 1}))).toNat =
            Module.finrank F (MvPolynomial (Fin n) F ⧸
              ((IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F)) ⊔
                Ideal.span {(X i : MvPolynomial (Fin n) F) - 1}))

end ObjectsChow

end GroundTheory.Heights₂.Heights
