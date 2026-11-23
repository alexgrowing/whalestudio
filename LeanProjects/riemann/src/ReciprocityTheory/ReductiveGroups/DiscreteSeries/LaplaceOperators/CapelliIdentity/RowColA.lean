import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.RowAnti
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ProdOfFnUpdateEq

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

theorem exists_perm_swap_succAbove {p : ℕ} (i s : Fin (p + 1)) (h : i ≠ s) :
    ∃ π : Equiv.Perm (Fin p), ((Equiv.Perm.sign π : ℤˣ) : ℤ) = (-1) ^ ((i : ℕ) + (s : ℕ) + 1) ∧
      ∀ t, Equiv.swap i s (i.succAbove t) = s.succAbove (π t) := by
  classical
  have hsa : ∀ (j : Fin (p + 1)) (u : Fin p), j.succAbove u = j.cycleRange.symm u.succ := fun j u =>
    ((Equiv.symm_apply_eq _).mpr (Fin.cycleRange_succAbove j u).symm).symm
  let ρ : Equiv.Perm (Fin (p + 1)) := s.cycleRange * Equiv.swap i s * i.cycleRange.symm
  have hρapp : ∀ x, ρ x = s.cycleRange (Equiv.swap i s (i.cycleRange.symm x)) := fun x => rfl
  have hρ0 : ρ 0 = 0 := by
    rw [hρapp, Fin.cycleRange_symm_zero, Equiv.swap_apply_left, Fin.cycleRange_self]
  let π : Equiv.Perm (Fin p) := (Equiv.Perm.decomposeFin ρ).2
  have hdec : Equiv.Perm.decomposeFin.symm ((Equiv.Perm.decomposeFin ρ).1, π) = ρ :=
    Equiv.Perm.decomposeFin.symm_apply_apply ρ
  have h1 : (Equiv.Perm.decomposeFin ρ).1 = 0 := by
    have := congrArg (fun g : Equiv.Perm (Fin (p + 1)) => g 0) hdec
    simp only [Equiv.Perm.decomposeFin_symm_apply_zero] at this
    rw [this, hρ0]
  rw [h1] at hdec
  refine ⟨π, ?_, ?_⟩
  · have hs : Equiv.Perm.sign ρ = Equiv.Perm.sign π := by
      rw [← hdec, Equiv.Perm.decomposeFin.symm_sign]
      simp
    have hs2 : Equiv.Perm.sign ρ = (-1) ^ (s : ℕ) * (-1) * (-1) ^ (i : ℕ) := by
      simp only [ρ, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
        Equiv.Perm.sign_swap h]
    rw [← hs, hs2]
    push_cast
    ring
  · intro t
    have h2 : (π t).succ = ρ t.succ := by
      rw [← hdec, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    rw [hsa s, h2, hρapp, ← hsa i, Equiv.symm_apply_apply]

theorem update_comp_succAbove {α : Type*} {p : ℕ} (f : Fin (p + 1) → α) (i : Fin (p + 1)) (t : Fin p) :
    Function.update (f ∘ i.succAbove) t (f i) = f ∘ Equiv.swap i (i.succAbove t) ∘ i.succAbove := by
  funext u
  by_cases hu : u = t
  · subst hu
    simp
  · simp only [Function.update_apply, if_neg hu, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succAbove_ne i u)
      (fun h => hu (Fin.succAbove_right_injective h))]

theorem sum_sum_succAbove {M : Type*} [AddCommGroup M] {p : ℕ} (f : Fin (p + 1) → M) :
    ∑ i : Fin (p + 1), ∑ t : Fin p, f (i.succAbove t) = p • ∑ s, f s := by
  have h : ∀ i : Fin (p + 1), ∑ t : Fin p, f (i.succAbove t) = ∑ s, f s - f i := by
    intro i
    rw [Fin.sum_univ_succAbove f i]
    abel
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [succ_nsmul]
  abel

theorem neg_one_pow_row (a b c : ℕ) :
    (-1 : ℂ) ^ (a + b) * (-1 : ℂ) ^ (a + c + 1) = (-1 : ℂ) ^ (c + b + 1) := by
  rw [← pow_add, show a + b + (a + c + 1) = (c + b + 1) + 2 * a by ring, pow_add, pow_mul]
  simp

theorem neg_one_pow_col (a b c : ℕ) :
    (-1 : ℂ) ^ (a + b) * (-1 : ℂ) ^ (b + c + 1) = (-1 : ℂ) ^ (a + c + 1) := by
  rw [← pow_add, show a + b + (b + c + 1) = (a + c + 1) + 2 * b by ring, pow_add, pow_mul]
  simp

section Ring

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem cminor_update_row {p : ℕ} (R : Fin (p + 1) → Fin n) (C : Fin p → Fin n) (i : Fin (p + 1))
    (t : Fin p) (y : ℂ) :
    cminor E (Function.update (R ∘ i.succAbove) t (R i)) C y =
      ((-1 : ℂ) ^ ((i : ℕ) + (i.succAbove t : ℕ) + 1)) • cminor E (R ∘ (i.succAbove t).succAbove) C y := by
  obtain ⟨π, hπ, hmap⟩ := exists_perm_swap_succAbove i (i.succAbove t) (Fin.succAbove_ne i t).symm
  have hrows : Function.update (R ∘ i.succAbove) t (R i) = (R ∘ (i.succAbove t).succAbove) ∘ π := by
    rw [update_comp_succAbove]
    funext u
    simp [hmap]
  rw [hrows, cminor_perm_rows, hπ, ← Int.cast_smul_eq_zsmul ℂ]
  simp

theorem cminor_update_col (hE : GlRelR E) {p : ℕ} (R : Fin p → Fin n) (C : Fin (p + 1) → Fin n)
    (j : Fin (p + 1)) (t : Fin p) (y : ℂ) :
    cminor E R (Function.update (C ∘ j.succAbove) t (C j)) y =
      ((-1 : ℂ) ^ ((j : ℕ) + (j.succAbove t : ℕ) + 1)) • cminor E R (C ∘ (j.succAbove t).succAbove) y := by
  obtain ⟨π, hπ, hmap⟩ := exists_perm_swap_succAbove j (j.succAbove t) (Fin.succAbove_ne j t).symm
  have hcols : Function.update (C ∘ j.succAbove) t (C j) = (C ∘ (j.succAbove t).succAbove) ∘ π := by
    rw [update_comp_succAbove]
    funext u
    simp [hmap]
  rw [hcols, cminor_perm_cols E hE, hπ, ← Int.cast_smul_eq_zsmul ℂ]
  simp

theorem capEntry_comm_sub (a b : Fin n) (x : ℂ) (X : 𝒰) :
    capEntry E x a b * X - X * capEntry E x a b = E a b * X - X * E a b := by
  unfold capEntry
  split_ifs
  · rw [add_mul, mul_add, Algebra.commutes]
    abel
  · simp

def capT {p : ℕ} (R C : Fin (p + 1) → Fin n) (y : ℂ) (s j : Fin (p + 1)) : 𝒰 :=
  if R s = C j then ((-1 : ℂ) ^ ((s : ℕ) + (j : ℕ) + 1)) • cminor E (R ∘ s.succAbove) (C ∘ j.succAbove) y
  else 0

theorem comm_term (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (i j : Fin (p + 1)) (y : ℂ) :
    ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
        (E (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) y -
          cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) y * E (R i) (C j)) =
      ∑ t, capT E R C y (i.succAbove t) j - ∑ t, capT E R C y i (j.succAbove t) := by
  rw [cminor_comm (hE := hE) (a := R i) (b := C j) (R := R ∘ i.succAbove)
    (C := C ∘ j.succAbove) (x := y), smul_sub, Finset.smul_sum, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [capT, Function.comp_apply]
    split_ifs with h
    · rw [cminor_update_row, smul_smul, neg_one_pow_row]
    · exact smul_zero _
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [capT, Function.comp_apply]
    by_cases h : C (j.succAbove t) = R i
    · rw [if_pos h, if_pos h.symm, cminor_update_col E hE, smul_smul, neg_one_pow_col]
    · rw [if_neg h, if_neg (Ne.symm h), smul_zero]

end Ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
