import Mathlib

noncomputable section

open Finset

namespace PositivityTheory.RgHe.Frame

variable {m : ℕ}

def pfR (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (j : Fin m) : ℝ :=
  (∏ i, (d' j - d i)) / ∏ k ∈ univ.erase j, (d' j - d' k)

def pfX (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) : ℝ := ∑ i, d i - ∑ j, d' j

def above (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (r : ℝ) : ℕ :=
  (univ.filter fun x : Fin (m + 1) ⊕ Fin m => r < Sum.elim d d' x).card

def pfD (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (i : Fin (m + 1)) : ℝ :=
  (∏ k ∈ univ.erase i, (d i - d k)) / ∏ j, (d i - d' j)

end PositivityTheory.RgHe.Frame
