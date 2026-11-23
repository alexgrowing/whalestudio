import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFeMat
import Development.DiscreteGroups.GlobalIrreducibility.DzFeDec

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

theorem sum_range_lt (n k : ℕ) : ∑ x ∈ Finset.range n, (if x < k then 1 else 0) = min n k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.lt_or_ge n k with h | h
    · rw [if_pos h, min_eq_left h.le, min_eq_left (by omega)]
    · rw [if_neg (by omega), min_eq_right h, min_eq_right (by omega), add_zero]

theorem card_SIdx : Fintype.card (SIdx m) = (m + 1) * m / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ k : Fin (m + 1), ∑ i : Fin (m + 1), (if (i, k).1 < (i, k).2 then 1 else 0) = (k : ℕ) := fun k => by
    show ∑ i : Fin (m + 1), (if (i : ℕ) < (k : ℕ) then 1 else 0) = (k : ℕ)
    rw [Fin.sum_univ_eq_sum_range (fun x => if x < (k : ℕ) then 1 else 0), sum_range_lt]
    exact min_eq_right k.2.le
  rw [Finset.sum_congr rfl (fun k _ => h k), Fin.sum_univ_eq_sum_range (fun x => x), Finset.sum_range_id]
  simp

theorem sum_range_between (n j m : ℕ) :
    ∑ x ∈ Finset.range n, (if j < x ∧ x < m then 1 else 0) = min n m - min n (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.min_def]
    split_ifs <;> omega

theorem card_WIdx (j : ℕ) : Fintype.card (WIdx m j) = m - 1 - j := by
  rw [Fintype.card_subtype, Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun x => if j < x ∧ x < m then 1 else 0), sum_range_between]
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem sum_split (j : ℕ) (f : ZMod g → ℂ) :
    ∑ b : JIdx m j → ZMod g, f (b (j0 m j)) =
      (Fintype.card ({i : JIdx m j // i ≠ j0 m j} → ZMod g) : ℂ) * ∑ s : ZMod g, f s := by
  rw [← (Equiv.funSplitAt (j0 m j) (ZMod g)).symm.sum_comp, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp [Equiv.funSplitAt_symm_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end DiscreteGroups.sglob.DzFe
