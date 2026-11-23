import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def LocalDimComponentBound.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), q ∈ zeroSet I →
    ∃ W : Ideal (MvPolynomial (Fin n) ℂ), W.IsPrime ∧ I ≤ W ∧ q ∈ zeroSet W ∧
      ringKrullDim (curveLocalRing I q) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W)

end

end GroundTheory.Heights₂.Heights
