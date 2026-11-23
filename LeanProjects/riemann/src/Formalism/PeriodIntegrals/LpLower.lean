import Mathlib

noncomputable section

namespace PI

def lpFeasible (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) : Set ℝ :=
  {y | ∃ xs : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ xs s i) ∧
    (∀ s i, (¬ Odd i ∨ d ≤ i) → xs s i = 0) ∧
    (∀ s, (∑ i ∈ Finset.range d, (l : ℝ) ^ i * xs s i) +
      (∑ i ∈ Finset.range d, xs (s - (i : ZMod d)) i) ≤ Ds s) ∧
    y = ∑ s, ∑ i ∈ Finset.range d, xs s i}

def lpF (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) : ℝ :=
  (l : ℝ) / ((l : ℝ) ^ 2 - 1) * (∑ s, Ds s) - sSup (lpFeasible l d Ds)

def LpLower : Prop :=
  ∀ (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ), 2 ≤ l → (∀ s, 0 ≤ Ds s) →
    (∑ s, Ds s) / ((l : ℝ) ^ 2 - 1) ≤ lpF l d Ds

end PI
