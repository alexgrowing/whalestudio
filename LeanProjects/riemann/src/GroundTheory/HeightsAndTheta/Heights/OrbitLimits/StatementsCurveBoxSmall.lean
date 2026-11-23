import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

def CurveBoxSmall.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k),
    IsArithVar (mCoordIdeal y) 1 → Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ (τ : ℕ) (s : Ω), IsSmallH (mCoordIdeal y) y A τ s ↔
      ∀ σ : Ω →+* ℂ, ‖σ (s / chartUnit y c A.a τ)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ

namespace CurveBoxSmall

end CurveBoxSmall

end GroundTheory.Heights₂.Heights.Targets
