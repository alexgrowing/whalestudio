import Mathlib

namespace PI

def PsiLeTwo : Prop := ∀ y : ℝ, 0 ≤ y → Chebyshev.psi y ≤ 2 * y

def PsiLower : Prop := ∀ u : ℝ, 2 ≤ u → 1 / 5 * u ≤ Chebyshev.psi u

def PrimeTailLogFour : Prop :=
  ∀ X : ℝ, 0 < X → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X < (p : ℝ)) →
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / X

end PI
