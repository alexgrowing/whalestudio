import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FSScaled
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel MvPolynomial

noncomputable section

def NmSmallIntoFS.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ (M k : ℕ) (C₀ : ℝ), 1 ≤ M ∧ 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ τ : ℕ,
      ∃ f : {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} →
          {σ : chartLat y (fsScaled ι C).a (M * (τ + k)) //
            IsSmallH (mCoordIdeal y) y (fsScaled ι C) (M * (τ + k)) (σ : Ω)},
        Function.Injective f

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
