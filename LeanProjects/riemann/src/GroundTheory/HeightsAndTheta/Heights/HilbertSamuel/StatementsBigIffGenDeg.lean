import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CoordinateSecondPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def BigIffGenDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (M : HermLine ι) (P₀ : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → P₀ ≤ mCoordIdeal y →
    IsSemipositiveRel P₀ (mCoordIdeal y) M →
    (IndefiniteRowSideFullHecke.HilbertSamuel.IsBig y M.a D ↔ 0 < genDeg (mCoordIdeal y) D M.a)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
