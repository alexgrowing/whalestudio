import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def GrowthOffHypersurfacePolynomial.Statement : Prop :=
  ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ) (M : ℕ), Q ≠ 0 →
    DifferentiableOn ℂ f {y | eval y Q ≠ 0} →
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 → ‖f y‖ ≤ C * (1 + ‖y‖) ^ M) →
    ∃ p : MvPolynomial (Fin d) ℂ, ∀ y : Fin d → ℂ, eval y Q ≠ 0 → f y = eval y p

end GroundTheory.Heights₂.Heights.HilbertSamuel
