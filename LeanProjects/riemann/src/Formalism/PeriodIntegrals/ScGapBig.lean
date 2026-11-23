import Mathlib

namespace PI.ScGapBig

def rk48 (k r : ℕ) : ℕ := 2 * r + k + 1

def GapBig (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ 1801 ≤ rk48 k r + t ∧
    ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j

def ScGapBig : Prop :=
  ∀ (k r : ℕ) (b : Fin (2 * r + 2) → ℝ), 1801 ≤ rk48 k r →
    (∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      16 * (rk48 k r : ℝ) ^ 19 ≤ b ⟨j.val + 1, hj⟩ - b j) →
    GapBig k r b

end PI.ScGapBig
