import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Counterexample.Objects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo Line

def MuMetricLine.Statement : Prop :=
  ∀ (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
    (c : ℝ) (hc : 0 < c) (z : (Σ _ : Unit, Fin 2) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      muMetric (lineHodgeScaled II hII c hc) z = Real.sqrt c

end GroundTheory.Heights₂.Heights.LowerBoundFree
