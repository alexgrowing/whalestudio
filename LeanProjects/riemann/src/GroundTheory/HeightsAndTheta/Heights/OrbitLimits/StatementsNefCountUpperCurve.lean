import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountUpper
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BirationalYPt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def NefCountUpperCurve.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    NefOnFibres (mCoordIdeal y) A.a → NefOnGeneric (mCoordIdeal y) A →
    HeightsNonneg II (mCoordIdeal y) A →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n ≤
        (II K ι (mCoordIdeal y) 1 (fun _ => A) + ε) * (n : ℝ)

end

end GroundTheory.Heights₂.Heights.Targets
