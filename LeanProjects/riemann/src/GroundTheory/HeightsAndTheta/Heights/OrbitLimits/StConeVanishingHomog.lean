import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ConeVanishingHomog.Statement : Prop :=
  ∀ (n : ℕ) (C : Set (Fin n → ℂ)), (∀ c ∈ C, ∀ a : ℂ, a ≠ 0 → a • c ∈ C) →
    IsHomogIdeal (MvPolynomial.vanishingIdeal ℂ C)

end GroundTheory.Heights₂.Heights
