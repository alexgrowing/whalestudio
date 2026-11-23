import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def MonicRootGrowth.Statement : Prop :=
  ∀ (d : ℕ) (m : Polynomial (MvPolynomial (Fin d) ℂ)), m.Monic →
    ∃ (C : ℝ) (M : ℕ), ∀ (y : Fin d → ℂ) (τ : ℂ), (m.map (eval y)).IsRoot τ →
      ‖τ‖ ≤ C * (1 + ‖y‖) ^ M

end GroundTheory.Heights₂.Heights.HilbertSamuel
