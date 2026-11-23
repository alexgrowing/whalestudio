import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

def InvDerivDecay.Statement : Prop :=
  ∀ (v G : ℂ → ℝ) (ρ R : ℝ), 0 < ρ → ContDiffOn ℝ 2 G (Metric.ball 0 ρ) →
    (∀ y : ℂ, R < ‖y‖ → v y = G y⁻¹) →
    ∃ C R₀ : ℝ, ∀ y : ℂ, R₀ < ‖y‖ →
      ‖fderiv ℝ v y‖ ≤ C / ‖y‖ ^ 2 ∧ ‖iteratedFDeriv ℝ 2 v y‖ ≤ C / ‖y‖ ^ 3

end GroundTheory.Heights₂.Heights.LowerBoundFree
