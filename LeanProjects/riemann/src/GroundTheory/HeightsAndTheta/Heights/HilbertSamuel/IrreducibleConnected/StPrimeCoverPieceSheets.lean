import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Matrix

def PrimeCoverPieceSheets.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d → ComplexSets.IsFiniteProjection W A →
      ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧ ∀ R : MvPolynomial (Fin d) ℂ, R ≠ 0 →
        ∀ (O F : Set (Fin n → ℂ)) (k : ℕ), IsOpen O → IsClosed F →
          {x | x ∈ ComplexSets.zeroSet W ∧ eval (A *ᵥ x) (P * R) ≠ 0} ∩ O =
            {x | x ∈ ComplexSets.zeroSet W ∧ eval (A *ᵥ x) (P * R) ≠ 0} ∩ F →
          (∀ y : Fin d → ℂ, eval y (P * R) ≠ 0 →
            {x | x ∈ ComplexSets.zeroSet W ∧ x ∈ O ∧ A *ᵥ x = y}.ncard = k) →
          k = 0 ∨ k = ComplexSets.projDegree W A

end GroundTheory.Heights₂.Heights.HilbertSamuel
