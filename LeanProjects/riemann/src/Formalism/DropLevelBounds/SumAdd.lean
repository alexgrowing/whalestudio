import Mathlib

noncomputable section
open scoped BigOperators

namespace Formalism.UnitaryBoundIntegral

def addl (k n f : ℕ) (l1 : ℝ) (l : ℕ) : ℝ :=
  if (l : ℝ) ^ 2 < k then (f : ℝ) * (n : ℝ) ^ 3 * (k : ℝ) ^ 3 * Real.log k
  else if (l : ℝ) < l1 then (f : ℝ) * (n : ℝ) ^ 3 * l * Real.log ((n : ℝ) * l) else 0

def SumAdd : Prop :=
  ∃ C : ℝ, ∀ (k n f N : ℕ) (T m b L : ℝ), 1 ≤ k → 1 ≤ n → 1 ≤ f → 0 < T → 0 < m → 0 < b → 0 < L →
    Real.log ((n : ℝ) * (Real.sqrt (m * b / (T * f * (n : ℝ) ^ 3)) / L)) ≤ L ^ 2 →
    T * f * (n : ℝ) ^ 3 * (k : ℝ) ^ 4 ≤ m * b →
    T * (∑ l ∈ (Finset.range (N + 1)).filter Nat.Prime,
      addl k n f (Real.sqrt (m * b / (T * f * (n : ℝ) ^ 3)) / L) l * Real.log l) ≤ C * m * b

end Formalism.UnitaryBoundIntegral
