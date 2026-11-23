import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology

noncomputable section

def PuncturedExpOrder.Statement : Prop :=
  ∀ (R : ℝ) (ψ : ℂ → ℂ) (k : ℤ) (M : ℝ), 0 < R → DifferentiableOn ℂ ψ (ball (0 : ℂ) R \ {0}) →
    (∀ x ∈ ball (0 : ℂ) R \ {0}, ‖Complex.exp (ψ x) * x ^ k‖ ≤ M) →
    0 ≤ k ∧ ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun x => Complex.exp (ψ x)) (𝓝[≠] 0) (𝓝 c)

end

end GroundTheory.Heights₂.Heights.Regular
