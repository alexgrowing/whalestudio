import Formalism.BranchSandwichDivisors.StatementR
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MemBranchRangeOfDefectEq

open Finset

namespace Formalism.BranchingDeterminantCap

theorem interlaceIdentities : InterlaceIdent := by
  intro n lam sg h
  have hsum : ∑ i, lam i = lam 0 + ∑ i : Fin n, lam i.succ := Fin.sum_univ_succ lam
  have hsum' : ∑ i, lam i = ∑ i : Fin n, lam i.castSucc + lam (Fin.last n) := Fin.sum_univ_castSucc lam
  have hd0 : d0 lam sg = ∑ i, sg i - ∑ i : Fin n, lam i.succ := by
    rw [d0, Finset.sum_sub_distrib]
  have hnn : ∀ i, 0 ≤ sg i - lam i.succ := fun i => by linarith [(h i).2]
  have h3 : 0 ≤ d0 lam sg := Finset.sum_nonneg fun i _ => hnn i
  have hle : ∀ i, sg i - lam i.succ ≤ d0 lam sg := fun i =>
    Finset.single_le_sum (f := fun i => sg i - lam i.succ) (fun j _ => hnn j) (Finset.mem_univ i)
  have h5 : ∀ i, sg i ∈ rset lam sg i := by
    intro i
    rw [rset, Finset.mem_Icc]
    have := (h i).1
    have := (h i).2
    have := hle i
    omega
  refine ⟨by linarith, ?_, h3, ?_, h5, ?_⟩
  · rw [Finset.sum_sub_distrib]; linarith
  · refine Finset.sum_nonneg fun i _ => ?_
    have := (h i).1
    have := (h i).2
    omega
  · intro i
    have hmem := h5 i
    rw [Finset.card_erase_of_mem hmem]
    rw [rset, Finset.mem_Icc] at hmem
    rw [rset, Int.card_Icc]
    have hc : 0 ≤ min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ := by omega
    have ht : ((min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ).toNat : ℤ) =
        min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ := Int.toNat_of_nonneg hc
    have h1 : 1 ≤ (min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ).toNat := by omega
    rw [Nat.cast_sub h1, ht]
    push_cast
    omega

theorem interlaceTelescope_statement : InterlaceTelescope := by
  intro n lam sg h p q hpq
  have hpq' := Fin.le_iff_val_le_val.mp hpq
  obtain ⟨k, hk⟩ : ∃ k, q.val = p.val + k := ⟨q.val - p.val, by omega⟩
  induction k generalizing q with
  | zero =>
    have : q = p := Fin.ext (by omega)
    subst this
    simp
  | succ k ih =>
    have hlt : p.val + k < n := by omega
    have hq1 : p ≤ (⟨p.val + k, hlt⟩ : Fin n) := Fin.le_iff_val_le_val.mpr (by simp)
    have ih' := ih ⟨p.val + k, hlt⟩ hq1 (by simp) rfl
    have hIcc : Finset.Icc p q = insert q (Finset.Icc p ⟨p.val + k, hlt⟩) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc, Fin.le_iff_val_le_val]; omega)]
    have hq := (h q).1
    have hcs : q.castSucc = (⟨p.val + k, hlt⟩ : Fin n).succ := Fin.ext (by simp; omega)
    rw [hcs] at hq
    linarith

end Formalism.BranchingDeterminantCap
