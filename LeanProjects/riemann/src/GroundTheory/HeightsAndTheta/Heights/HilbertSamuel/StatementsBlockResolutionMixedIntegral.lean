import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BlockResolutionMetricObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockResolutionMixedIntegral.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : HermLine ι), A'.a = unitDeg d.k₀ → IsSmoothHerm A' →
    ∑ i ∈ Finset.range (D + 1),
        ptsIntegral (mCoordIdeal d.y) (blockMixPot d.A A' D i) (fun z => Real.log (A'.h z / d.A.h z)) =
      ((D : ℝ) + 1) * blockMetricInt d A'

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
