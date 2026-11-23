import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FSScaled
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel MvPolynomial

noncomputable section

def FSSmallCountBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    ∀ C : ℝ, 1 ≤ C → ∃ R : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      smallSectionCount (IsSmallH (mCoordIdeal y) y (fsScaled ι C)) (chartLat y (fsScaled ι C).a) n ≤
        R * (n : ℝ) ^ (D + 1)

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
