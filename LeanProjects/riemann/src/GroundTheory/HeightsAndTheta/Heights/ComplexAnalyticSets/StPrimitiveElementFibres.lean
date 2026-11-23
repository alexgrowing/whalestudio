import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def PrimitiveElementFibres.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ (c : Fin n → ℂ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Δ : MvPolynomial (Fin d) ℂ)
        (Q : Fin n → Polynomial (MvPolynomial (Fin d) ℂ)),
        m.Monic ∧ m.natDegree = projDegree J A ∧ Δ ≠ 0 ∧
          ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
            (m.map (eval y)).Separable ∧
            (∀ x ∈ fibre J A y, (m.map (eval y)).IsRoot (∑ j, c j * x j) ∧
              ∀ j, eval y Δ * x j = ((Q j).map (eval y)).eval (∑ j, c j * x j)) ∧
            ∀ τ : ℂ, (m.map (eval y)).IsRoot τ → ∃ x ∈ fibre J A y, ∑ j, c j * x j = τ

end

end GroundTheory.Heights₂.Heights.ComplexSets
