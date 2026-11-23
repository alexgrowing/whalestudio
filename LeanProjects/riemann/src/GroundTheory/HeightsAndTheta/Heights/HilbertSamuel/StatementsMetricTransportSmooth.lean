import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def MetricTransportSmooth.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)),
    IsInvMat B → IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) → IsSmoothMetric m'

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
