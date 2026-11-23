import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Example
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def LocalOrbitChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (y : (Σ k, ι k) → Ω) (n : ℕ), IsArithVar (mCoordIdeal y) (n + 1) → SmoothGenericFibreM y →
    ∀ z₀ ∈ mcPts (mCoordIdeal y), ∃ N : Set ((Σ k, ι k) → ℂ), IsOpen N ∧ z₀ ∈ N ∧
      ∃ κ : ((Σ k, ι k) → ℂ) → (Fin n → ℂ), AnalyticOnNhd ℂ κ N ∧
        (∀ z ∈ N, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ N ∧ κ (torusSmul c z) = κ z) ∧
        ∀ z ∈ N ∩ mcPts (mCoordIdeal y), ∀ z' ∈ N ∩ mcPts (mCoordIdeal y), κ z = κ z' →
          ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z' = torusSmul c z

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
