import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftSectionSeparation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → ∀ (n : ℕ) (s : Ω),
      s ∈ chartLat y (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a n → s ≠ 0 →
      ∀ c : ℝ, c < Real.exp (-(C * n * ((q : ℝ) + 1))) →
        ¬ IsBoundedH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) (q : ℤ) 1) n c s

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
