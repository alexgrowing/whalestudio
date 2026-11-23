import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def PointSliceMass.Statement : Prop :=
  ∀ (n δ : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin 1 × Fin n) ℂ) (ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J 1 f → IsMultiHomog δ f → linForm ℓ ∉ J →
      varInt (J ⊔ Ideal.span {linForm ℓ - 1}) 0 (fun _ => 1)
        (fun _ x => Real.log (h.dualNorm x)) = δ

end

end GroundTheory.Heights₂.Heights
