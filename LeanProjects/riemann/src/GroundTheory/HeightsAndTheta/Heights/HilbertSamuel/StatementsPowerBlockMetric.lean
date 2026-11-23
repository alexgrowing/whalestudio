import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (P0 : Ideal (MRing ι)) (m N : ℕ) (v : Fin N → Ω),
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    ∃ (B : HermLine (addIdx ι N)) (P0' : Ideal (MRing (addIdx ι N))),
      B.a = unitDeg (none : Option K) ∧ IsConjInvariantH B ∧ P0' ≤ mCoordIdeal (addBlock y v) ∧
      IsSemipositiveRel P0' (mCoordIdeal (addBlock y v)) B ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
        secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
