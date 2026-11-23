import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ConeSliceIdeal.Statement : Prop :=
  ∀ (n : ℕ) (C : Set (Fin n → ℂ)) (t : Fin n → ℂ) (V : Ideal (MvPolynomial (Fin n) ℂ)),
    (∀ c ∈ C, ∀ a : ℂ, a ≠ 0 → a • c ∈ C) → MvPolynomial.vanishingIdeal ℂ C ≤ V →
      MvPolynomial.vanishingIdeal ℂ {x | x ∈ C ∧ MvPolynomial.eval x (linForm t) = 1} ≤
        V ⊔ Ideal.span {linForm t - 1}

end GroundTheory.Heights₂.Heights
