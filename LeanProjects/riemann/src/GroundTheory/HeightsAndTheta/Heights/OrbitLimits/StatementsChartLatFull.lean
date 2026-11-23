import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def ChartLatFull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [NumberField Ω]
    (y : (Σ k, ι k) → Ω), Birational y →
    ∀ (a : K → ℤ) (τ : ℕ) (s : Ω), ∃ n : ℕ, 0 < n ∧ (n : Ω) * s ∈ chartLat y a τ

end GroundTheory.Heights₂.Heights.Targets
