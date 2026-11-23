import Mathlib

namespace PI

def DepthLegendre : Prop :=
  (∀ p : ℕ, p.Prime → ∀ c : ℕ, 1 ≤ c → (p - 1) * padicValNat p c.factorial < c) ∧
  (∀ p : ℕ, 2 ≤ p → ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ≤ 2 * ((p : ℝ) ^ n - 1) / ((p : ℝ) - 1) ∧
      (n : ℝ) - 1 ≤ 2 * ((p : ℝ) ^ (n - 1) - 1) / ((p : ℝ) - 1))

end PI
