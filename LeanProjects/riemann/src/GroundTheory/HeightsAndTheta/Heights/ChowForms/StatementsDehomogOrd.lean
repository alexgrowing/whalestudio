import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartIncOrd
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncidenceZeroLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def DehomogOrd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsHomogIdeal I → IsHomogIdeal W → I ≤ W → linForm t ∉ W →
    ∀ [(W.map (Ideal.Quotient.mk I)).IsPrime]
      [(W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))).IsPrime]
      (g : MvPolynomial (Fin n) F) (d : ℕ), g.IsHomogeneous d →
      Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk I)))
          (algebraMap _ _ (Ideal.Quotient.mk I g)) =
        Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))))
          (algebraMap _ _ (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}) g))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
