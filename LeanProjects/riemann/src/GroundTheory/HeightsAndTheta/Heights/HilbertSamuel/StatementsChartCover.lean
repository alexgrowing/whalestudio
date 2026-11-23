import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def ChartTaylorCover.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A),
    ∃ r : ℝ, 0 < r ∧ ∃ M c : ℝ, 0 < c ∧ ∀ x : X, ∃ j : Fin A.n, x ∈ (A.chart j).source ∧
      Metric.closedBall (A.chart j x) r ⊆ (A.chart j).target ∧
      (∀ y ∈ Metric.closedBall (A.chart j x) r, c ≤ dV.dens j y) ∧
      ∀ W ∈ [W₀, W₁], ∃ ℓ : (Fin D → ℂ) →L[ℝ] ℝ, ∀ z : Fin D → ℂ, ‖z‖ ≤ r →
        W.φ j ((A.chart j).symm (A.chart j x + z)) ≤ W.φ j x + ℓ z + M * ∑ i, ‖z i‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
