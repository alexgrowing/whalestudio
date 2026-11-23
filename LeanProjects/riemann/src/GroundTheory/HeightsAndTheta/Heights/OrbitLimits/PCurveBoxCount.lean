import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxSmall
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

theorem CurveBoxCount.proof (hS : CurveBoxSmall.Statement) (hL : CurveBoxLattice.Statement) :
    CurveBoxCount.Statement := by
  intro K _ ι _ Ω _ y A c R hP hB hA hc hR hRu
  obtain ⟨C, hC⟩ := hL K ι Ω y A c R hP hB hA hc hR hRu
  refine ⟨C, fun τ hτ => ?_⟩
  have e : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ =
      Real.log (Nat.card {s : chartLat y A.a τ //
        ∀ σ : Ω →+* ℂ, ‖σ ((s : Ω) / chartUnit y c A.a τ)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ}) := by
    unfold smallSectionCount
    rw [Nat.card_congr (Equiv.subtypeEquivRight (p := fun s : chartLat y A.a τ => IsSmallH (mCoordIdeal y) y A τ (s : Ω))
      fun s => hS K ι Ω y A c hP hB hc τ (s : Ω))]
  rw [e]
  exact hC τ hτ

end GroundTheory.Heights₂.Heights.Targets
