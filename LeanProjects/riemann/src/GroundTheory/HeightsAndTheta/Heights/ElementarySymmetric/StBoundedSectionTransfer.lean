import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.ArithNMInhabitants
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def BoundedSectionTransfer.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω Ω' : Type) [Field Ω] [Field Ω']
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι k) → Ω') (d : ℕ) (A : Geo.HermLine ι) (τ : ℕ) (c : ℝ) (s' : Ω'),
    IsArithVar (mCoordIdeal y) d → mCoordIdeal y' = mCoordIdeal y →
    s' ∈ chartLat y' A.a τ → s' ≠ 0 → IsBoundedH (mCoordIdeal y') y' A τ c s' →
    ∃ s ∈ chartLat y A.a τ, s ≠ 0 ∧ IsBoundedH (mCoordIdeal y) y A τ c s

end

end GroundTheory.Heights₂.Heights.Targets
