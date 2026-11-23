import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveDiscriminant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n d : ℕ}

def FunctionFieldDegree.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    IsFiniteProjection J A →
    letI := projAlgebra J A
    ∀ (K L : Type) [Field K] [Field L] [Algebra (MvPolynomial (Fin d) ℂ) K]
      [IsFractionRing (MvPolynomial (Fin d) ℂ) K] [Algebra (MvPolynomial (Fin n) ℂ ⧸ J) L]
      [IsFractionRing (MvPolynomial (Fin n) ℂ ⧸ J) L] [Algebra (MvPolynomial (Fin d) ℂ) L]
      [Algebra K L] [IsScalarTower (MvPolynomial (Fin d) ℂ) K L]
      [IsScalarTower (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) L],
      FiniteDimensional K L ∧ Module.finrank K L = projDegree J A ∧
        IntermediateField.adjoin K
          (Set.range fun j => algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) L (Ideal.Quotient.mk J (X j))) = ⊤

end

end GroundTheory.Heights₂.Heights.ComplexSets
