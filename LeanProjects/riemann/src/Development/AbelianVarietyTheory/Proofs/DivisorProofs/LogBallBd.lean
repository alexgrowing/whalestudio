import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace GlobalTheory.LogMean

def LogBallBd {E : Type} [PseudoMetricSpace E] [MeasureSpace E] (f : E → ℝ) (x₀ : E) (k : ℕ) : Prop :=
  ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ x ∈ Metric.closedBall x₀ δ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ →
    IntegrableOn f (Metric.ball x ρ) ∧ ∫ y in Metric.ball x ρ, f y ≤ C * ρ ^ k * (1 + Real.log (1 / ρ))

theorem LogBallBd.shrink {E : Type} [PseudoMetricSpace E] [MeasureSpace E] {f : E → ℝ} {x₀ : E} {k : ℕ}
    (h : LogBallBd f x₀ k) {ε : ℝ} (hε : 0 < ε) : ∃ δ C : ℝ, 0 < δ ∧ δ ≤ ε ∧ 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall x₀ δ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ →
        IntegrableOn f (Metric.ball x ρ) ∧ ∫ y in Metric.ball x ρ, f y ≤ C * ρ ^ k * (1 + Real.log (1 / ρ)) := by
  obtain ⟨δ, C, hδ, hC, h⟩ := h
  refine ⟨min δ ε, C, lt_min hδ hε, min_le_right _ _, hC, fun x hx ρ hρ hρδ => ?_⟩
  exact h x (Metric.closedBall_subset_closedBall (min_le_left _ _) hx) ρ hρ (hρδ.trans (min_le_left _ _))

end GlobalTheory.LogMean
