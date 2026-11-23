import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def UnbranchedPartConnected.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d → ComplexSets.IsFiniteProjection W A →
      ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧ ∀ R : MvPolynomial (Fin d) ℂ, R ≠ 0 →
        IsPreconnected {x : Fin n → ℂ | x ∈ ComplexSets.zeroSet W ∧ eval (A.mulVec x) (P * R) ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
