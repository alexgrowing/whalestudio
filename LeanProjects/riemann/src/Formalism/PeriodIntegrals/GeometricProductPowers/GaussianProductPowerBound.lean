import Mathlib

noncomputable section

namespace ConditionalKappaBounds.G2

def GaussianProductPowerBound : Prop := ∀ (f k r : ℕ) (b g0 g1 : ℝ), 1 ≤ f → f ≤ k → 2 ≤ b →
  ((k : ℝ) * b) ^ 8 ≤ g0 → ((k : ℝ) * b) ^ 8 ≤ g1 →
  (1 - (((f : ℝ) * k) ^ 3)⁻¹ / 4) * (g0 * g1) ^ (f * (r * (r - 1) / 2)) ≤
    (∏ i ∈ Finset.Ico 1 r, ((g0 ^ i - 1) * (g1 ^ i - 1))) ^ f

end ConditionalKappaBounds.G2
