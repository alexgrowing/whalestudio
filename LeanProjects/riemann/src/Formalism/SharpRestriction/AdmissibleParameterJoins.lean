import Formalism.SharpRestriction.GlobalTheoremInputs

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.D5

theorem loss_bound_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ L.B0 := by
  have h : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  unfold SizeData₂.B0 sizeBudget bSize
  positivity

theorem Nc_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ L.Nc := by
  have h : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  unfold SizeData₂.Nc budgetNc rankBudget bSize
  positivity

end Formalism.MainNotions
