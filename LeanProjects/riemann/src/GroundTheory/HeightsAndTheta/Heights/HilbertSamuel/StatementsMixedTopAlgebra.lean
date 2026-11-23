import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

def MixedTopAlgebra.Statement : Prop :=
  ∀ (d : ℕ) (m : ℕ → ℝ), 2 ≤ d → (∀ i, 1 ≤ i → i ≤ d → 0 ≤ m i) → 0 < m d →
    (∀ q p : ℕ, 1 ≤ q → 1 ≤ p →
      0 < ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * (q : ℝ) ^ (d - i) * (p : ℝ) ^ i * m i →
      0 ≤ ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * (q : ℝ) ^ (d - 1 - i) * (p : ℝ) ^ i * m i) →
    0 ≤ m 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
