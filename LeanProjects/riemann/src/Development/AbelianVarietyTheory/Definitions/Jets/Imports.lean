import Mathlib

open Finset

noncomputable section

namespace GlobalTheory.WigSh

def wP {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) (l : Fin (n + 1)) : ℝ :=
  (∏ j, ((M j : ℝ) - 1 - (L l : ℝ))) / ∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))

def wM {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) (l : Fin (n + 1)) : ℝ :=
  (∏ j, ((M j : ℝ) - (L l : ℝ))) / ∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))

end GlobalTheory.WigSh
