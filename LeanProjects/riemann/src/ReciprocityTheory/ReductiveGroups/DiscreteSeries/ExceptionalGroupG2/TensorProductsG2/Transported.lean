import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def thrS (ε : Fin n → Bool) : ℝ :=
  max (2 * (n : ℝ))
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))

end ReciprocityTheory.ChartRestriction.DS.G2
