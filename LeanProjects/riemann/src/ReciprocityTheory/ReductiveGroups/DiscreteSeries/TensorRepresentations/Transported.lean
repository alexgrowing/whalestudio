import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def thrStar (ε : Fin n → Bool) : ℝ :=
  max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))

end ReciprocityTheory.ChartRestriction.DS
