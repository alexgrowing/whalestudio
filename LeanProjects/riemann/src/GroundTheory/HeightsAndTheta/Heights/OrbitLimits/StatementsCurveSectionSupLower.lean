import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BirationalYPt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def CurveSectionSupLower.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y → IsSmoothHerm A →
    ∀ (n : ℕ) (s : Ω), s ∈ chartLat y A.a n → s ≠ 0 → ∀ c : ℝ, IsBoundedH (mCoordIdeal y) y A n c s →
      Real.exp (-((n : ℝ) * II K ι (mCoordIdeal y) 1 (fun _ => A) /
        (Module.finrank ℤ (chartLat y A.a n) : ℝ))) ≤ c

namespace CurveSectionSupLower

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end CurveSectionSupLower

end

end GroundTheory.Heights₂.Heights.Targets
