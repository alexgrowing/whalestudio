import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeSp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ipf.Val.SphM

def aCo (q c t k j : ℕ) : ℂ :=
  (q : ℂ) ^ ((c - j) * (k - j)) * (Formalism.L2.Col.gaussBin q t (k - j) : ℂ) * (((Real.sqrt q : ℝ) : ℂ) ^ c)⁻¹ ^ k *
    (((Real.sqrt q : ℝ) : ℂ) ^ (c + t)) ^ j

end GlobalTheory.CompanionTheory.Ipf.Val.SphM

end
