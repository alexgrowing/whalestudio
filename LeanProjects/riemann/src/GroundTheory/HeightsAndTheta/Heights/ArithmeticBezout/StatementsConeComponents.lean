import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemMinimalPrimesOfMemFundCycleSupport
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

def ConeIntegralComponents.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℂ),
    IsArithVar P (e + 1) → (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W) →
      ∑ W ∈ (fundCycle (complexFibreIdeal P)).support, coneIntegral h W e (fsLog h u) =
        coneIntegral h (complexFibreIdeal P) e (fsLog h u)

end GroundTheory.Heights₂.Heights
