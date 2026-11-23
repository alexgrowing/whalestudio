import Mathlib

namespace PI

open Finset

def vandN (x : ℕ → ℝ) (N : ℕ) : ℝ := ∏ i ∈ range N, ∏ j ∈ Ico (i + 1) N, (x i - x j)

noncomputable def dimVN (x : ℕ → ℝ) (N : ℕ) : ℝ := vandN x N / ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ)

def shiftSeq {n : ℕ} (w : Fin n → ℤ) : ℕ → ℝ := fun i => if h : i < n then ((w ⟨i, h⟩ : ℤ) : ℝ) - i else 0

def WeylProd : Prop :=
  ∀ (n : ℕ) (μ w : Fin n → ℤ) (c : ℤ), (∀ t, μ t = w t - c) →
    (((∏ i : Fin n, ∏ j : Fin n,
      if i < j then (((μ i : ℤ) : ℚ) - ((μ j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1 : ℚ)) : ℝ) = dimVN (shiftSeq w) n

end PI
