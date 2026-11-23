import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SectionHyperplaneAvoid.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    IsProjPrime J → ∃ ℓ : Fin n → ℂ, linForm ℓ ∉ J ∧ ∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W

end

end GroundTheory.Heights₂.Heights
