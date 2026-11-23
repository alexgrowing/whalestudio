import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.RowCol

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → 𝒰)

theorem expand_cons_succAbove_eq (c : Fin (m + 1)) :
    (Fin.cons c c.succAbove : Fin (m + 1) → Fin (m + 1)) = id ∘ ⇑(Fin.cycleRange c).symm := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Fin.cycleRange_symm_zero]
  · simp [Fin.cycleRange_symm_succ]

theorem expand_sign_cycleRange_symm (c : Fin (m + 1)) :
    (((Equiv.Perm.sign (Fin.cycleRange c).symm : ℤˣ) : ℤ) : ℂ) = (-1 : ℂ) ^ (c : ℕ) := by
  rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  push_cast
  rfl

theorem expand_cons_not_inj {b c : Fin (m + 1)} (h : b ≠ c) :
    ¬ Function.Injective (Fin.cons b c.succAbove : Fin (m + 1) → Fin (m + 1)) := by
  intro hinj
  obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq h
  have h0 : (Fin.cons b c.succAbove : Fin (m + 1) → Fin (m + 1)) 0 =
      (Fin.cons b c.succAbove : Fin (m + 1) → Fin (m + 1)) z.succ := by
    simp [hz]
  exact Fin.succ_ne_zero z (hinj h0).symm

theorem capelli_expand_plus (hE : GlRelR E) (om : ℂ) (b c : Fin (m + 1)) :
    ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E om d b * cminor E d.succAbove c.succAbove (om - 1)) =
      if b = c then capelliC E om else 0 := by
  have key : cminor E id (Fin.cons b c.succAbove : Fin (m + 1) → Fin (m + 1)) om =
      ∑ d : Fin (m + 1), ((-1 : ℂ) ^ (d : ℕ)) •
        (capEntry E om d b * cminor E d.succAbove c.succAbove (om - 1)) := by
    rw [cminor_succ_col]
    rfl
  have hsum : ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E om d b * cminor E d.succAbove c.succAbove (om - 1)) =
      ((-1 : ℂ) ^ (c : ℕ)) • ∑ d : Fin (m + 1), ((-1 : ℂ) ^ (d : ℕ)) •
        (capEntry E om d b * cminor E d.succAbove c.succAbove (om - 1)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_smul, pow_add, mul_comm]
  rw [hsum, ← key]
  by_cases hbc : b = c
  · subst hbc
    rw [if_pos rfl, expand_cons_succAbove_eq, cminor_perm_cols (E := E) hE,
      ← Int.cast_smul_eq_zsmul ℂ, expand_sign_cycleRange_symm, smul_smul, ← pow_add, ← two_mul,
      pow_mul, neg_one_sq, one_pow, one_smul]
    rfl
  · rw [if_neg hbc, cminor_cols_not_inj (E := E) hE _ _ _ (expand_cons_not_inj hbc), smul_zero]

theorem capelli_expand_minus (hE : GlRelR E) (om : ℂ) (a c : Fin (m + 1)) :
    ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E (om - (m : ℂ)) a d * cminor E c.succAbove d.succAbove om) =
      if a = c then capelliC E om else 0 := by
  have key : cminor E (Fin.cons a c.succAbove : Fin (m + 1) → Fin (m + 1)) id om =
      ∑ d : Fin (m + 1), ((-1 : ℂ) ^ (d : ℕ)) •
        (capEntry E (om - (m : ℂ)) a d * cminor E c.succAbove d.succAbove om) := by
    rw [cminor_succ_row (E := E) hE]
    rfl
  have hsum : ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E (om - (m : ℂ)) a d * cminor E c.succAbove d.succAbove om) =
      ((-1 : ℂ) ^ (c : ℕ)) • ∑ d : Fin (m + 1), ((-1 : ℂ) ^ (d : ℕ)) •
        (capEntry E (om - (m : ℂ)) a d * cminor E c.succAbove d.succAbove om) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_smul, pow_add, mul_comm]
  rw [hsum, ← key]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, expand_cons_succAbove_eq, cminor_perm_rows (E := E),
      ← Int.cast_smul_eq_zsmul ℂ, expand_sign_cycleRange_symm, smul_smul, ← pow_add, ← two_mul,
      pow_mul, neg_one_sq, one_pow, one_smul]
    rfl
  · rw [if_neg hac, cminor_rows_not_inj (E := E) _ _ _ (expand_cons_not_inj hac), smul_zero]

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
