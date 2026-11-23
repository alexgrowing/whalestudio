import Mathlib
import Formalism.HermitianCurvature.StatementQ

open Matrix Finset

namespace PI.QnCovHat2W

open Formalism.REAL Formalism.FourierDecayAlt.Q

noncomputable def sgnL {r : ℕ} {α : Type*} [DecidableEq α] (x e : Fin r → α) : ℂ :=
  Matrix.det (Matrix.of fun k j => if x k = e j then (1 : ℂ) else 0)

theorem sum_fun_succ {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (f : (Fin (r + 1) → α) → M) :
    ∑ x, f x = ∑ x0 : α, ∑ y : Fin r → α, f (Fin.cons x0 y) := by
  rw [← (Fin.consEquiv fun _ : Fin (r + 1) => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sgnL_eq_sum {r : ℕ} {α : Type*} [DecidableEq α] (x e : Fin r → α) :
    sgnL x e = ∑ σ : Equiv.Perm (Fin r),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (if x = e ∘ σ.symm then 1 else 0) := by
  unfold sgnL
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  congr 1
  simp only [Matrix.of_apply]
  rw [Finset.prod_boole]
  by_cases h : x = e ∘ σ.symm
  · rw [if_pos h, if_pos]
    intro i _
    rw [h]
    simp
  · rw [if_neg h, if_neg]
    intro H
    apply h
    funext j
    have h1 := H (σ.symm j) (Finset.mem_univ _)
    simpa using h1

theorem sum_sgnL {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin r → α) (g : (Fin r → α) → M) :
    ∑ x, sgnL x e • g x = ∑ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) • g (e ∘ π) := by
  simp_rw [sgnL_eq_sum, Finset.sum_smul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun σ => by simp [Equiv.Perm.sign_inv, Equiv.Perm.inv_def])

theorem sum_sgnL_alt {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin r → α) (F : (Fin r → α) → M)
    (hF : ∀ (x : Fin r → α) (π : Equiv.Perm (Fin r)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x) :
    ∑ x, sgnL x e • F x = (r.factorial : ℂ) • F e := by
  rw [sum_sgnL]
  have h1 : ∀ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) • F (e ∘ π) = F e := by
    intro π
    rw [hF, smul_smul]
    have h2 : ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign π : ℤ) : ℂ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    rw [h2, one_smul]
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ]

theorem sum_sgnL_succ {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin (r + 1) → α) (H : (Fin (r + 1) → α) → M) :
    ∑ x, sgnL x e • H x = ∑ j : Fin (r + 1), ((-1 : ℂ) ^ (j : ℕ)) •
      ∑ y : Fin r → α, sgnL y (e ∘ j.succAbove) • H (Fin.cons (e j) y) := by
  have hexp : ∀ (x0 : α) (y : Fin r → α), sgnL (Fin.cons x0 y : Fin (r + 1) → α) e =
      ∑ j : Fin (r + 1), (-1 : ℂ) ^ (j : ℕ) *
        ((if x0 = e j then 1 else 0) * sgnL y (e ∘ j.succAbove)) := by
    intro x0 y
    unfold sgnL
    rw [Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
    congr 2
    all_goals first
      | (simp [Matrix.of_apply]; done)
      | (congr 1; ext k j'; simp [Matrix.submatrix_apply, Matrix.of_apply])
  have step : ∀ (x0 : α) (y : Fin r → α),
      sgnL (Fin.cons x0 y : Fin (r + 1) → α) e • H (Fin.cons x0 y) =
        ∑ j : Fin (r + 1), if x0 = e j then
          ((-1 : ℂ) ^ (j : ℕ) • (sgnL y (e ∘ j.succAbove) • H (Fin.cons (e j) y))) else 0 := by
    intro x0 y
    rw [hexp, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · subst h
      rw [one_mul, mul_smul]
    · rw [zero_mul, mul_zero, zero_smul]
  rw [sum_fun_succ]
  simp_rw [step]
  conv_lhs => arg 2; ext x0; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp

theorem skip_two_of_lt {m : ℕ} (j : Fin (m + 2)) (j' : Fin (m + 1)) (h : Fin.castSucc j' < j) :
    (fun k : Fin m => j.succAbove (j'.succAbove k)) = skip2 (Fin.castSucc j') j := by
  funext k
  apply Fin.ext
  simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.coe_castSucc, Fin.val_succ] at h ⊢
  split_ifs <;> (try simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_mk, Fin.lt_def] at *) <;> omega

theorem skip_two_of_ge {m : ℕ} (j : Fin (m + 2)) (j' : Fin (m + 1)) (h : j ≤ Fin.castSucc j') :
    (fun k : Fin m => j.succAbove (j'.succAbove k)) = skip2 j j'.succ := by
  funext k
  apply Fin.ext
  simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.coe_castSucc, Fin.val_succ] at h ⊢
  split_ifs <;> (try simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_mk, Fin.lt_def, Fin.le_def] at *) <;> omega

theorem sum_two {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin (m + 2) → α) (F : (Fin m → α) → M)
    (hF : ∀ (x : Fin m → α) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x)
    (β β' : α → ℂ) :
    ∑ c : Fin (m + 2) → α, sgnL c e • ((β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ)) =
      ∑ j : Fin (m + 2), ∑ j' : Fin (m + 1),
        ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β (e j) * β' (e (j.succAbove j'))) * (m.factorial : ℂ)) •
          F (fun k => e (j.succAbove (j'.succAbove k))) := by
  refine (sum_sgnL_succ e (fun c => (β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ))).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := sum_sgnL_succ (e ∘ j.succAbove)
    (fun y : Fin (m + 1) → α => (β (e j) * β' (y 0)) • F (fun k => y k.succ))
  simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Function.comp_apply] at h2 ⊢
  rw [h2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  have h3 : ∑ z : Fin m → α, sgnL z ((e ∘ j.succAbove) ∘ j'.succAbove) •
      ((β (e j) * β' (e (j.succAbove j'))) • F z) =
      (β (e j) * β' (e (j.succAbove j'))) • ((m.factorial : ℂ) • F ((e ∘ j.succAbove) ∘ j'.succAbove)) := by
    simp_rw [smul_comm (sgnL _ _) (β (e j) * β' (e (j.succAbove j')))]
    rw [← Finset.smul_sum, sum_sgnL_alt _ F hF]
  rw [h3, smul_smul, smul_smul, smul_smul, pow_add]
  congr 1

theorem reindex_pairs {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → M) (β β' : Fin (m + 2) → ℂ) :
    ∑ j : Fin (m + 2), ∑ j' : Fin (m + 1),
        ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β j * β' (j.succAbove j'))) •
          F (fun k => j.succAbove (j'.succAbove k)) =
      ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
          F (skip2 i i') else 0 := by
  have hR : ∀ i : Fin (m + 2), ∑ i' : Fin (m + 2),
      (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
        F (skip2 i i') else 0) =
      ∑ i' : Fin (m + 2), (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i)) •
        F (skip2 i i') else 0) -
      ∑ i' : Fin (m + 2), (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i * β' i')) •
        F (skip2 i i') else 0) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i' _ => ?_
    split_ifs
    · rw [mul_sub, sub_smul]
    · rw [sub_zero]
  have hL : ∀ j : Fin (m + 2), ∑ j' : Fin (m + 1),
      ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β j * β' (j.succAbove j'))) •
        F (fun k => j.succAbove (j'.succAbove k)) =
      ∑ i : Fin (m + 2), (if i < j then ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (β j * β' i)) •
        F (skip2 i j) else 0) -
      ∑ i' : Fin (m + 2), (if j < i' then ((-1 : ℂ) ^ ((j : ℕ) + (i' : ℕ)) * (β j * β' i')) •
        F (skip2 j i') else 0) := by
    intro j
    rw [Fin.sum_univ_castSucc (f := fun i => if i < j then ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) *
        (β j * β' i)) • F (skip2 i j) else 0),
      Fin.sum_univ_succ (f := fun i' => if j < i' then ((-1 : ℂ) ^ ((j : ℕ) + (i' : ℕ)) *
        (β j * β' i')) • F (skip2 j i') else 0)]
    simp only [not_lt.mpr (Fin.le_last j), Fin.not_lt_zero, if_false, add_zero, zero_add]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases h : Fin.castSucc j' < j
    · have h' : ¬ j < j'.succ := by
        rw [← Fin.le_castSucc_iff]
        exact not_le.mpr h
      rw [if_pos h, if_neg h', sub_zero, Fin.succAbove_of_castSucc_lt _ _ h, skip_two_of_lt j j' h,
        Fin.val_castSucc]
      congr 1
      ring
    · have hle : j ≤ Fin.castSucc j' := not_lt.mp h
      have h' : j < j'.succ := Fin.le_castSucc_iff.mp hle
      rw [if_neg h, if_pos h', zero_sub, Fin.succAbove_of_le_castSucc _ _ hle, skip_two_of_ge j j' hle,
        Fin.val_succ, ← neg_smul]
      congr 1
      ring
  rw [Finset.sum_congr rfl fun j _ => hL j, Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun i _ => hR i, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]

end PI.QnCovHat2W
