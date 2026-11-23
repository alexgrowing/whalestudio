import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open Finset

def gauss (q : ℝ) (N k : ℕ) : ℝ :=
  (∏ j ∈ range k, (q ^ (N - j) - 1)) / ∏ j ∈ range k, (q ^ (j + 1) - 1)

variable {q : ℝ}

def wt (N : ℕ) (S : Finset (Fin N)) : ℕ := ∑ i ∈ S, (N - 1 - (i : ℕ))

def pw (q : ℝ) (N : ℕ) (S : Finset (Fin N)) : ℝ := q ^ wt N S / q ^ S.card.choose 2

end SatakeBound

end GroundTheory.BlockD
