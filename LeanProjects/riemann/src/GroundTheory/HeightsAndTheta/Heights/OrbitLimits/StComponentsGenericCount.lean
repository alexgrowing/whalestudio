import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

def ComponentsGenericCount.Statement : Prop :=
  ∀ (n d : ℕ) (F : Finset (Ideal (MvPolynomial (Fin n) ℂ))) (A : Matrix (Fin d) (Fin n) ℂ),
    (∀ J ∈ F, J.IsPrime ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ) ∧ IsFiniteProjection J A) →
    (∀ J ∈ F, ∀ J' ∈ F, J ≤ J' → J = J') →
      (∀ y : Fin d → ℂ,
        {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard ≤ ((∑ J ∈ F, projDegree J A : ℕ) : ℕ∞)) ∧
      ∃ Δ : MvPolynomial (Fin d) ℂ, Δ ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
        {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard = ((∑ J ∈ F, projDegree J A : ℕ) : ℕ∞) ∧
        ∀ x, (∃ J ∈ F, x ∈ zeroSet J) → A *ᵥ x = y →
          ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ ∀ y' ∈ U, A *ᵥ g y' = y' ∧ ∃ J ∈ F, g y' ∈ zeroSet J

end GroundTheory.Heights₂.Heights
