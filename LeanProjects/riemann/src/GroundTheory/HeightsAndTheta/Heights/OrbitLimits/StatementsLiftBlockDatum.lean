import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def liftCoords {ι' : Type} [Fintype ι'] {Ω : Type} (x' : ι' → Ω) : Fin (Fintype.card ι') → Ω :=
  fun j => x' ((Fintype.equivFin ι').symm j)

def LiftBlockDatum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (a : ℕ)
    (ι' : Type) [Fintype ι'] (x' : ι' → Ω),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    1 ≤ a → (∀ j, x' j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) x' →
    Birational (fun p : Σ _ : Unit, ι' => x' p.2) →
    ∃ d : HSMBlockDatum D (Option K) (addIdx ι (Fintype.card ι')) Ω,
      d.y = addBlock y (liftCoords x') ∧ d.k₀ = none ∧
      (∀ z ∈ mcPts (mCoordIdeal d.y), ∀ j : Fin (Fintype.card ι'),
        secNormAt y N a (liftCoords x' j) (basePart₂ z) * d.A.h z = ‖z ⟨none, j⟩‖) ∧
      ∀ w ∈ mcPts (mCoordIdeal y), ∃ z ∈ mcPts (mCoordIdeal d.y), basePart₂ z = w

end

end GroundTheory.Heights₂.Heights.Targets
