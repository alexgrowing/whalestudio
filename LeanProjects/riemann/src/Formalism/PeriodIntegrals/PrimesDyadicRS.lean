import Mathlib

namespace PI.PrimesDyadicRS

def Claim : Prop :=
  ∀ y : ℝ, 41 / 2 ≤ y →
    3 * y / (5 * Real.log y) < (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)

end PI.PrimesDyadicRS
