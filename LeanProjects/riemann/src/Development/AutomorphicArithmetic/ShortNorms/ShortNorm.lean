import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

noncomputable section

namespace UpperTheory.T3

def ShortNorm : Prop :=
  ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (d M : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → 1 ≤ X →
    Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 →
    c' * h * X / ((4 * (d : ℝ) * (M : ℝ) ^ 2) ^ A * Real.log X) ≤ ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ)

def SmallOne : Prop := ∃ A : ℝ, 1 ≤ A ∧ ∀ M : ℕ, 2 ≤ M → ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (M : ℝ) ^ A

def ModAt (x eps : ℝ) (N d : ℕ) : Prop :=
  d.Prime ∧ d % 4 = 3 ∧ 100 ≤ d ∧ 0 < N ∧ d ∣ N ∧ Real.log N ≤ 3 * x ^ (eps / 5) * Real.log x ^ 2

end UpperTheory.T3

end
