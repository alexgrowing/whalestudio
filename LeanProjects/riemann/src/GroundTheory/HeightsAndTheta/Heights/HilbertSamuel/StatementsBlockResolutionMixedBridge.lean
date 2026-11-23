import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BlockResolutionMetricObjects
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionMixedBridge.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (L : Fin D → HermLine ι) (A₁ : HermLine ι),
    (∀ j, IsSmoothHerm (L j)) → A₁.a = unitDeg d.k₀ → IsSmoothHerm A₁ →
    ptsIntegral (mCoordIdeal d.y) (fun j z => Real.log ((L j).h z)) (fun z => Real.log (A₁.h z / d.A.h z)) =
      mInt d.R.A (fun j => AnResBridge.potOf d.R (L j))
        (fun x => Real.log (A₁.h (blockPt d x) / d.A.h (blockPt d x)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
