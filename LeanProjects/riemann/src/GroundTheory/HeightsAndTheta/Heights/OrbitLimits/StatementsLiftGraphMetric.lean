import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftBlockDatum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftGraphMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (a r : ℕ) (v : Fin r → Ω),
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    (∀ j, v j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) v →
    ∃ A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι r), A.a = unitDeg (none : Option K) ∧ IsConjInvariantH A ∧
      IsSemipositiveRel (mCoordIdeal (addBlock y v)) (mCoordIdeal (addBlock y v)) A ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin r,
        secNormAt y N a (v j) (basePart₂ z) * A.h z = ‖z ⟨none, j⟩‖

end

end GroundTheory.Heights₂.Heights.Targets
