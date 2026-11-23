import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def PrimePairMeetImage.Statement : Prop :=
  ∀ (n d : ℕ) (Q Q' : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ),
    Q.IsPrime → Q'.IsPrime → Q ≠ Q' →
    (∀ y : Fin d → ℂ, (ComplexSets.fibre Q A y).Finite) →
    (∀ y : Fin d → ℂ, (ComplexSets.fibre Q' A y).Finite) →
      ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧
        ∀ x ∈ ComplexSets.zeroSet Q ∩ ComplexSets.zeroSet Q', eval (A.mulVec x) e = 0

end GroundTheory.Heights₂.Heights
