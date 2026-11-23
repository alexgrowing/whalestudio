import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsConeAvoid
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LinearFormCut.Statement : Prop :=
  ∀ (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
      ∃ B : Matrix (Fin 1) (Fin n) ℂ,
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (I ⊔ linIdeal B)) ≤ (e : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.ComplexSets
