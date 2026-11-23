import Development.DiscreteGroups.GlobalIrreducibility.MulRowOfGood

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

theorem good_colU (j : ℕ) (c : Fin n → k) : Good j ((colU j c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  rw [val_colU, Matrix.add_apply, colM_apply, if_neg (by omega), add_zero]

theorem good_colU_inv (j : ℕ) (c : Fin n → k) :
    Good j (((colU j c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [colU_inv]; exact good_colU j _

theorem peel_apply (j : ℕ) (hj : j < n) (g : GL (Fin n) k) (i l : Fin n) :
    ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i l =
      (g : Matrix (Fin n) (Fin n) k) i l + (if i.val < j then
        -(g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ * (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ l else 0) := by
  rw [Units.val_mul, colU_mul_apply j hj]
  rfl

theorem peel_N (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) {g : GL (Fin n) k} (hg : g ∈ Nset j) :
    colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g ∈ Nset (j + 1) ∧
    sdS j (g : Matrix (Fin n) (Fin n) k) =
      sdS (j + 1) ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) + (g : Matrix (Fin n) (Fin n) k) ⟨j - 1, by omega⟩ ⟨j, hj⟩ := by
  have hg' : ∀ i l : Fin n, (l ≤ i ∨ l.val < j) → (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := hg
  have hjj : (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ ⟨j, hj⟩ = 1 := by rw [hg' _ _ (Or.inl le_rfl), one_apply_eq]
  have hrow : ∀ l : Fin n, l.val < j → (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ l = 0 := fun l hl => by
    rw [hg' _ _ (Or.inr hl), one_apply_ne]; intro h; rw [← h] at hl; simp at hl
  have hhi : ∀ i l : Fin n, j ≤ i.val → ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) i l = (g : Matrix (Fin n) (Fin n) k) i l := fun i l hi => by
    rw [peel_apply, if_neg (by omega), add_zero]
  refine ⟨fun i l hil => ?_, ?_⟩
  · rw [peel_apply]
    by_cases hl : l.val < j
    · rw [hg' i l (Or.inr hl), hrow l hl]; simp
    · by_cases hlj : l.val = j
      · have hl' : l = ⟨j, hj⟩ := Fin.ext hlj
        subst hl'
        by_cases hi : i.val < j
        · rw [if_pos hi, hjj, mul_one, add_neg_cancel, one_apply_ne]
          intro h; rw [h] at hi; simp at hi
        · rw [if_neg hi, add_zero]
          exact hg' i _ (Or.inl (by rw [Fin.le_iff_val_le_val]; simp; omega))
      · have hli : l ≤ i := hil.resolve_right (by omega)
        rw [if_neg (by rw [Fin.le_iff_val_le_val] at hli; omega), add_zero]
        exact hg' i l (Or.inl hli)
  · have key : ∀ i l : Fin n, (if l.val = i.val + 1 ∧ j ≤ l.val then (g : Matrix (Fin n) (Fin n) k) i l else 0) =
        (if l.val = i.val + 1 ∧ j + 1 ≤ l.val then ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
          Matrix (Fin n) (Fin n) k) i l else 0) +
        (if i = (⟨j - 1, by omega⟩ : Fin n) then (if l = (⟨j, hj⟩ : Fin n) then (g : Matrix (Fin n) (Fin n) k) i l else 0) else 0) := by
      intro i l
      by_cases h2 : l.val = i.val + 1 ∧ j + 1 ≤ l.val
      · rw [if_pos ⟨h2.1, by omega⟩, if_pos h2, hhi i l (by omega),
          if_neg (fun h => by rw [Fin.ext_iff] at h; simp at h; omega), add_zero]
      · rw [if_neg h2, zero_add]
        by_cases h1 : l.val = i.val + 1 ∧ j ≤ l.val
        · have e1 : i = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
          have e2 : l = ⟨j, hj⟩ := Fin.ext (by simp; omega)
          rw [if_pos h1, if_pos e1, if_pos e2]
        · rw [if_neg h1]
          by_cases e1 : i = ⟨j - 1, by omega⟩
          · by_cases e2 : l = ⟨j, hj⟩
            · exfalso; apply h1; rw [e1, e2]; simp; omega
            · rw [if_pos e1, if_neg e2]
          · rw [if_neg e1]
    rw [sdS, sdS]
    simp only [key, Finset.sum_add_distrib]
    congr 1
    simp

end DiscreteGroups.sglob.LConvGenM
