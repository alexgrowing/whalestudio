import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemMinimalPrimesOfMemFundCycleSupport
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

def ConeChartIntegrable.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℂ),
    IsArithVar P (e + 1) → (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W) →
      IntegrableOn (fun y => fsLog h u (h.pointOf y))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ complexFibreIdeal P, eval (h.pointOf y) q = 0}
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))

end GroundTheory.Heights₂.Heights
