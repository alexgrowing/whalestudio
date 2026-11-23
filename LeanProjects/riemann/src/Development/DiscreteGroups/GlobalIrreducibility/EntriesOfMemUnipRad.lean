import Development.DiscreteGroups.GlobalIrreducibility.GoodColUInv

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

theorem entries_of_mem_unipRad (j : ℕ) (h : ∑ i, ![j, n - j] i = n) {g : GL (Fin n) k}
    (hg : g ∈ unipRad k (stdBlocks ![j, n - j] h)) (i l : Fin n) (hil : ¬ (i.val < j ∧ j ≤ l.val)) :
    (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
  refine GlobalTheory.ThetaRad.mem_unipRad_iff_entries.1 hg i l ?_
  rw [GlobalTheory.ThetaRad.blk_stdBlocks_two, GlobalTheory.ThetaRad.blk_stdBlocks_two]
  by_cases hi : i.val < j
  · have hl : l.val < j := by omega
    simp [hi, hl]
  · simp only [hi, if_false]
    split_ifs <;> decide

theorem peel_rad (j : ℕ) (hj : j < n) (h : ∑ i, ![j, n - j] i = n) {g : GL (Fin n) k}
    (hg : g ∈ unipRad k (stdBlocks ![j, n - j] h)) :
    colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g ∈ Nset (j + 1) ∧
    sdS (j + 1) ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = 0 := by
  have hent := entries_of_mem_unipRad j h hg
  have key : ∀ i l : Fin n, ¬ (i.val < j ∧ j + 1 ≤ l.val) →
      ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
    intro i l hil
    rw [peel_apply]
    by_cases hi : i.val < j
    · rw [if_pos hi, hent ⟨j, hj⟩ l (by simp)]
      by_cases hlj : l.val = j
      · have hl' : l = ⟨j, hj⟩ := Fin.ext hlj
        subst hl'
        rw [one_apply_eq, mul_one, add_neg_cancel, one_apply_ne]
        intro e; rw [e] at hi; simp at hi
      · have hne : (⟨j, hj⟩ : Fin n) ≠ l := fun e => hlj (by rw [← e])
        rw [one_apply_ne hne, mul_zero, add_zero, hent i l (by omega)]
    · rw [if_neg hi, add_zero, hent i l (by omega)]
  refine ⟨fun i l hil => key i l (by
    rcases hil with hil | hil
    · rw [Fin.le_iff_val_le_val] at hil; omega
    · omega), ?_⟩
  rw [sdS]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
  split_ifs with hh
  · rw [key i l (by omega), one_apply_ne]
    intro e; rw [e] at hh; omega
  · rfl

def TopLeft (j : ℕ) (x : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i l : Fin n, (j ≤ i.val ∨ j ≤ l.val) → x i l = (1 : Matrix (Fin n) (Fin n) k) i l

theorem TopLeft.good {j : ℕ} {x : Matrix (Fin n) (Fin n) k} (hx : TopLeft j x) : Good j x :=
  fun i l h => hx i l (by omega)

def dotj (j : ℕ) (ξ c : Fin n → k) : k := ∑ i : Fin n, if i.val < j then ξ i * c i else 0

def rowMul (j : ℕ) (ξ : Fin n → k) (Y : Matrix (Fin n) (Fin n) k) : Fin n → k :=
  fun a => ∑ i : Fin n, if i.val < j then ξ i * Y i a else 0

def colMul (j : ℕ) (Y : Matrix (Fin n) (Fin n) k) (c : Fin n → k) : Fin n → k :=
  fun i => ∑ a : Fin n, if a.val < j then Y i a * c a else 0

theorem dotj_colMul (j : ℕ) (ξ c : Fin n → k) (Y : Matrix (Fin n) (Fin n) k) :
    dotj j ξ (colMul j Y c) = dotj j (rowMul j ξ Y) c := by
  let F : Fin n → Fin n → k := fun i a => if i.val < j ∧ a.val < j then ξ i * Y i a * c a else 0
  have hL : dotj j ξ (colMul j Y c) = ∑ i : Fin n, ∑ a : Fin n, F i a := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val < j
    · rw [if_pos hi, colMul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by by_cases ha : a.val < j <;> simp [F, hi, ha, mul_assoc]
    · rw [if_neg hi]; simp [F, hi]
  have hR : dotj j (rowMul j ξ Y) c = ∑ a : Fin n, ∑ i : Fin n, F i a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a.val < j
    · rw [if_pos ha, rowMul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by by_cases hi : i.val < j <;> simp [F, hi, ha]
    · rw [if_neg ha]; simp [F, ha]
  rw [hL, hR, Finset.sum_comm]

end DiscreteGroups.sglob.LConvGenM
