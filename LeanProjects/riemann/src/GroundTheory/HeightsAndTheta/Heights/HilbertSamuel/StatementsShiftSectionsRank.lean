import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology

noncomputable section

def ShiftSectionsRank.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A →
    ∀ q : ℕ, 1 ≤ q →
      Tendsto (fun n : ℕ =>
          (Module.finrank ℤ (chartLat y (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a n) : ℝ) /
            ((n : ℝ) ^ D / (D.factorial : ℝ))) atTop
        (𝓝 (genDeg (mCoordIdeal y) D (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
