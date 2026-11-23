import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore

noncomputable section

open Polynomial

namespace Formalism.L2.SG.Pf.GoodRecipPf

section Rev

variable {K : Type*} [Field K]

theorem rev_natDegree {q : K[X]} (h : q.coeff 0 ≠ 0) : q.reverse.natDegree = q.natDegree := by
  have ht : q.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr h)
  rw [reverse_natDegree, ht, Nat.sub_zero]

theorem rev_rev {q : K[X]} (h : q.coeff 0 ≠ 0) : q.reverse.reverse = q := by
  have hn := rev_natDegree h
  show (q.reverse).reflect q.reverse.natDegree = q
  rw [hn]
  show (reflect q.natDegree q).reflect q.natDegree = q
  exact reflect_reflect

end Rev

section Inv

variable {L : Type*} [Field L]

end Inv

section Recip

variable {g : ℕ} [Fact g.Prime]

end Recip

end Formalism.L2.SG.Pf.GoodRecipPf

namespace Formalism.L2.SG.Pf.RowDictPf

open Formalism.L2.SG.Pf.GoodRecipPf

end Formalism.L2.SG.Pf.RowDictPf
