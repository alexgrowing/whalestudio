import Mathlib

noncomputable section

namespace PI

def pr (y : ℝ) : Finset ℕ := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime

def PrimeCountBound : Prop := ∀ y : ℝ, 1 < y → ((pr y).card : ℝ) < 1.26 * y / Real.log y

end PI
