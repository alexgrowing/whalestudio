import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchInCurveComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch I 1 q),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ J ∈ I.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) ∧
        ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), c.toFun t ∈ zeroSet J

end

end GroundTheory.Heights₂.Heights
