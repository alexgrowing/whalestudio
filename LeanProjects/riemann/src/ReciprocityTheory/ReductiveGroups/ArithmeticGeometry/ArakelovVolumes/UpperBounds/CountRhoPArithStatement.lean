import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

def CountRhoPArithStatement : Prop :=
  ∀ (n T δ dV dW : ℕ), 1 ≤ n → 11 * n ^ 2 ≤ T → dW ≤ dV →
    δ * (T + n).choose n ≤ dW → dV ≤ δ * (T + 2 * n + 6).choose n →
    ((dV : ℝ) - dW) ≤ (n : ℝ) * (n + 6) * dV / T

def CountRhoArithStatement : Prop :=
  ∀ (n T δ dV ρ : ℕ), 1 ≤ n → 11 * n ^ 2 ≤ T →
    δ * (T - 1).choose n + ρ ≤ dV → dV ≤ δ * (T + 2 * n + 6).choose n →
    (ρ : ℝ) ≤ 22 * (n : ℝ) ^ 2 * dV / T

end ReciprocityTheory.ChartRestriction.G.AR.Up
