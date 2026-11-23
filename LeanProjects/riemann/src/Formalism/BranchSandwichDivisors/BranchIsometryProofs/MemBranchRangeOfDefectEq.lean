import Formalism.BranchSandwichDivisors.StatementR

open Finset

namespace Formalism.BranchingDeterminantCap

theorem memBranchRangeOfDefectEq : ConstituentRange := by
  unfold ConstituentRange
  intro n lam sg mu h1 h2 h3 i
  unfold Interlace at h1 h2
  have hmu := h2 i
  have hle : mu i - lam i.succ ≤ d0 lam mu := by
    unfold d0
    exact Finset.single_le_sum (f := fun j => mu j - lam j.succ)
      (fun j _ => sub_nonneg.mpr (h2 j).2) (Finset.mem_univ i)
  unfold rset
  rw [Finset.mem_Icc]
  refine ⟨hmu.2, le_min hmu.1 ?_⟩
  linarith

end Formalism.BranchingDeterminantCap
