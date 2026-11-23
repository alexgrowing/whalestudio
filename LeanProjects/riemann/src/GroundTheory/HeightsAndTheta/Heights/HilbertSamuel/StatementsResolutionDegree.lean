import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionMetricObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionDegree.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (m : ConeMetric ℂ (Ix κ)), IsProjFrame d.x e → IsSmoothMetric m →
    mInt d.R.A (fun _ => resPot d m) (fun _ => 1) = (projDeg d.x e : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
