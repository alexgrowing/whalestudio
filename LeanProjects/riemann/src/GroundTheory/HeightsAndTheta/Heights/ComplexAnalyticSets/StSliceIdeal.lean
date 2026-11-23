import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SliceIdeal.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (F : MvPolynomial (Fin (k + 1) × Fin n) ℂ)
    (ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (k + 1) F → linForm ℓ ∉ J →
      (J ⊔ Ideal.span {linForm ℓ - 1}).IsPrime ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) = (k : ℕ) ∧
        ∀ u : Fin n → ℂ, linForm u ∉ J → linForm u ∉ J ⊔ Ideal.span {linForm ℓ - 1}

end

end GroundTheory.Heights₂.Heights
