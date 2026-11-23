import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def StdGap (ε : Fin n → Bool) (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∃ h : ℝ, GapAtLeast ε lam h ∧ 2 * (n : ℝ) < h

end ReciprocityTheory.ChartRestriction.DS.G2
