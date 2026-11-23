import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionMetricObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResolutionMixedIntegral.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)), IsSmoothMetric m₁ →
    ∑ i ∈ Finset.range (D + 1),
        ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ d.x) (mixPot d.m m₁ D i) (logRatio d.m m₁) =
      ((D : ℝ) + 1) * resMetricInt d m₁

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
