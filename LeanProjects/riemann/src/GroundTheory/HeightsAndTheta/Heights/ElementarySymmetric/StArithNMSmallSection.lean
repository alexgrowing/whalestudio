import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsArithNakaiMoishezon
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def ArithNMSmallSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) L → IsConjInvariantH L →
    IsAmpleOnModel y L.a →
    0 < II K ι (mCoordIdeal y) (D + 1) (fun _ => L) →
    ∃ m : ℕ, 1 ≤ m ∧ ∃ s ∈ chartLat y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m).a 1, s ≠ 0 ∧
      ∃ c : ℝ, c < 1 ∧ IsBoundedH (mCoordIdeal y) y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m) 1 c s

end

end GroundTheory.Heights₂.Heights.Targets
