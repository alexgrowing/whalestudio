import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n d : ℕ}

abbrev projAlgebra (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
  (projHom J A).toRingHom.toAlgebra

def sum₂ (c : Fin n → ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (c j) * X j

def formMinpoly (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (c : Fin n → ℂ) :
    Polynomial (MvPolynomial (Fin d) ℂ) :=
  letI := projAlgebra J A
  minpoly (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J (sum₂ c))

def PrimitiveDiscriminant.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ D : MvPolynomial (Fin n) ℂ, D ≠ 0 ∧ ∀ c : Fin n → ℂ, eval c D ≠ 0 →
        (formMinpoly J A c).Monic ∧ (formMinpoly J A c).natDegree = projDegree J A ∧
        Polynomial.eval₂ (pullback A).toRingHom (sum₂ c) (formMinpoly J A c) ∈ J ∧
        (formMinpoly J A c).discr ≠ 0 ∧
        ∀ j : Fin n, ∃ G : Polynomial (MvPolynomial (Fin d) ℂ),
          pullback A (formMinpoly J A c).discr * X j -
            Polynomial.eval₂ (pullback A).toRingHom (sum₂ c) G ∈ J

end

end GroundTheory.Heights₂.Heights.ComplexSets
