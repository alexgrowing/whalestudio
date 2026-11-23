import Mathlib

noncomputable section
open scoped BigOperators

namespace Formalism.UnitaryBoundIntegral

def thl (k l : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ i : ℕ, Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i ∧ t = ((l : ℝ) ^ i)⁻¹}

def ThBounds : Prop :=
  ∀ (k l : ℕ), 1 ≤ k → 2 ≤ l →
    thl k l ≤ ((l : ℝ) ^ 3)⁻¹ ∧ thl k l < ((k : ℝ) ^ ((3 : ℝ) / 2))⁻¹ ∧
      ((k : ℝ) < (l : ℝ) ^ 2 → thl k l = ((l : ℝ) ^ 3)⁻¹)

def SumTh : Prop :=
  ∃ C : ℝ, ∀ (k N : ℕ), 1 ≤ k →
    (∑ l ∈ (Finset.range (N + 1)).filter Nat.Prime, thl k l * Real.log l) ≤ C / k

end Formalism.UnitaryBoundIntegral
