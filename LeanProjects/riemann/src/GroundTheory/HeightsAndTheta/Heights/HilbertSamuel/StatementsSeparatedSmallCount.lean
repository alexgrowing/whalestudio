import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SeparatedSmallCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (τ : ℕ) (b : ℝ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → 0 ≤ b →
    (∀ s : Ω, s ∈ chartLat y A.a τ → s ≠ 0 → ∀ c : ℝ, c < Real.exp (-b) →
      ¬ IsBoundedH (mCoordIdeal y) y A τ c s) →
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ ≤
      (Module.finrank ℤ (chartLat y A.a τ) : ℝ) * (b + Real.log 3)

section Inhabitant

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end Inhabitant

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
