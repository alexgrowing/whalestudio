import Formalism.SharpRestriction.Divisibility.SchurIrreducible

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace Formalism.L2.Theta

def NoncompactGapAtLeastRange (p q : ℕ) (lam : Ix p q → ℚ) : Prop := ∃ h : ℝ, GapGe lam h ∧ rangeOfSeventhSum p q ≤ h

def sparBound (n p q : ℕ) : ℝ := max (2 * (n : ℝ)) (8 * (n : ℝ) * ((min p q : ℕ) : ℝ))

def SParGap (n p q : ℕ) (S : SPar) : Prop :=
  p = 0 ∨ q = 0 ∨ ∃ h : ℝ, sparBound n p q < h ∧
    ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h ≤ |((x.1 : ℚ) : ℝ) - ((y.1 : ℚ) : ℝ)|

theorem sParGap_of_definite {n p q : ℕ} (h : p = 0 ∨ q = 0) (S : SPar) : SParGap n p q S := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end Formalism.L2.Theta

end
