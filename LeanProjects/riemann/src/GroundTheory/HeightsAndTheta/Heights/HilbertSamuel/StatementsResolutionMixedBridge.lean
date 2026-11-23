import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionMetricObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionMixedBridge.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (M : Fin D → ConeMetric ℂ (Ix κ)) (m₁ : ConeMetric ℂ (Ix κ)),
    (∀ j, IsSmoothMetric (M j)) → IsSmoothMetric m₁ →
    ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ d.x) (fun j z => Real.log ((M j).ρ z)) (logRatio d.m m₁) =
      mInt d.R.A (fun j => resPot d (M j)) (fun y => logRatio d.m m₁ (resPt d y))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
