import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def NefSmallSectionEventually.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    NefOnFibres (mCoordIdeal y) A.a → NefOnGeneric (mCoordIdeal y) A →
    HeightsNonneg II (mCoordIdeal y) A →
    0 < II K ι (mCoordIdeal y) (D + 1) (fun _ => A) →
    ∀ᶠ n : ℕ in atTop, ∃ t ∈ chartLat y A.a n, t ≠ 0 ∧ IsSmallH (mCoordIdeal y) y A n t

def NefSmallSectionEventually.oneSystem : IntersectionSystem := fun _ _ _ _ _ _ _ => 1

end

end GroundTheory.Heights₂.Heights.Targets
