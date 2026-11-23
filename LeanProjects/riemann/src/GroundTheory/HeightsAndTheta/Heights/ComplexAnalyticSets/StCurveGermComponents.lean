import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def CurveGermComponents.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet I ∩ N, ∃ W ∈ I.minimalPrimes,
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1 ∧ q ∈ zeroSet W ∧ x ∈ zeroSet W

end

end GroundTheory.Heights₂.Heights
