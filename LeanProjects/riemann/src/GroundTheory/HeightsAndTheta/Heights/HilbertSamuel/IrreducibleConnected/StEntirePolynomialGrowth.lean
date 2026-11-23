import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def EntirePolynomialGrowth.Statement : Prop :=
  ∀ (d : ℕ) (f : (Fin d → ℂ) → ℂ) (C : ℝ) (M : ℕ), Differentiable ℂ f →
    (∀ y : Fin d → ℂ, ‖f y‖ ≤ C * (1 + ‖y‖) ^ M) →
    ∃ p : MvPolynomial (Fin d) ℂ, ∀ y : Fin d → ℂ, f y = eval y p

end GroundTheory.Heights₂.Heights.HilbertSamuel
