import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def DominantPrimitiveFibres.Statement : Prop :=
  ∀ (n d : ℕ) (Q : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), Q.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤ ((d : ℕ) : WithBot ℕ∞) →
    Function.Injective (ComplexSets.projHom Q A) →
      ∃ (c : Fin n → ℂ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Δ : MvPolynomial (Fin d) ℂ)
        (S : Fin n → Polynomial (MvPolynomial (Fin d) ℂ)),
        Δ ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
          (m.map (eval y)).natDegree = m.natDegree ∧ (m.map (eval y)).Separable ∧
          (∀ x ∈ ComplexSets.fibre Q A y, (m.map (eval y)).IsRoot (∑ j, c j * x j) ∧
            ∀ j, eval y Δ * x j = ((S j).map (eval y)).eval (∑ k, c k * x k)) ∧
          ∀ τ : ℂ, (m.map (eval y)).IsRoot τ → ∃ x ∈ ComplexSets.fibre Q A y, ∑ j, c j * x j = τ

end GroundTheory.Heights₂.Heights
