import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def RootGridLower.Statement : Prop :=
  ∀ (e m : ℕ) (Q : MvPolynomial (Fin e) ℤ), Q ≠ 0 → (∀ i, Q.degreeOf i < m) →
    ∃ ζ : Fin e → ℂ, (∀ i, ζ i ^ m = 1) ∧ 1 ≤ ‖eval ζ (map (Int.castRingHom ℂ) Q)‖

end GroundTheory.Heights₂.Heights.HilbertSamuel
