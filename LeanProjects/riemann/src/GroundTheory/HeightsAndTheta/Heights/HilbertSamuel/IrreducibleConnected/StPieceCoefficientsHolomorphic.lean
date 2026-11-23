import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StPieceRootProductPolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Matrix

def PieceCoefficientsHolomorphic.Statement : Prop :=
  ∀ (n d N : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (Z : Set (Fin n → ℂ)) (c : Fin n → ℂ)
    (Q : MvPolynomial (Fin d) ℂ) (O F : Set (Fin n → ℂ)),
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 →
      {x | x ∈ Z ∧ A *ᵥ x = y}.Finite ∧ {x | x ∈ Z ∧ A *ᵥ x = y}.ncard = N ∧
      ∀ x ∈ Z, A *ᵥ x = y → ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
          DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A *ᵥ g w = w) ∧ Z ∩ V = g '' U) →
    IsOpen O → IsClosed F →
    {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ O = {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ F →
    ∀ i : ℕ, DifferentiableOn ℂ
      (fun y : Fin d → ℂ => (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i) {y | eval y Q ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
