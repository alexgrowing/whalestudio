import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BlockResolutionMetricObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionDegreeIntegral.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A₀ A₁ : HermLine ι),
    A₀.a = unitDeg d.k₀ → A₁.a = unitDeg d.k₀ → IsSmoothHerm A₀ → IsSmoothHerm A₁ →
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      mInt d.R.A (fun _ => blockInterpPot d A₀ A₁ t) (fun _ => 1) =
        (genDeg (mCoordIdeal d.y) D (unitDeg d.k₀) : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
