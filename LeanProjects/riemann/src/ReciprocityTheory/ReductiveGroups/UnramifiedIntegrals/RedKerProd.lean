import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKerIdeal

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem kerProd (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    (hl : l.Prime) (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (e : ℕ) (he : e = 2 ∨ e = 3 ∧ d ≠ 3) :
    KerProdAt d L l e := by
  rcases he with he | ⟨he, hd3⟩
  · exact kerProd_prin d L hd4 hCM l hl h5 hld e (Or.inl he)
  · by_cases h3 : 3 ∣ d
    · subst he
      exact kerProd_ideal d L hsq hd4 hCM l hl h3 hd3
    · exact kerProd_prin d L hd4 hCM l hl h5 hld e (Or.inr ⟨he, h3⟩)

end ReciprocityTheory.ChartRestriction.L1
