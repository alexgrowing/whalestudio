import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SectionDegreeSum.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e δ : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 2) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 2) f → IsMultiHomog δ f → linForm u ∉ I →
      ∃ (g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin (e + 1) × Fin n) F)
        (δW : Ideal (MvPolynomial (Fin n) F) → ℕ),
        (∀ W ∈ (divCycle I u).support,
          IsProjPrime W ∧ IsChowForm W (e + 1) (g W) ∧ IsMultiHomog (δW W) (g W)) ∧
        δ = ∑ W ∈ (divCycle I u).support, divCycle I u W * δW W

end

end GroundTheory.Heights₂.Heights
