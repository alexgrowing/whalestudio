import Mathlib
import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.RotationOfDiagonalGenerator
set_option maxSynthPendingDepth 1

open Polynomial Formalism.REAL

namespace GroundTheory.BlockD.FourierDecayAlt.GaugeExists

noncomputable section

section Capelli

variable {A : Type} [Ring A] [Algebra ℂ A]

def tmPoly {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) : A[X] :=
  (if a = b then X - C (algebraMap ℂ A (k : ℂ)) else 0) + C (E a b)

def qdetPoly {n : ℕ} (E : Fin n → Fin n → A) : A[X] :=
  ∑ σ : Equiv.Perm (Fin n), C ((Equiv.Perm.sign σ : ℤ) : A) *
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod

def evU (u : ℂ) : A[X] →+* A :=
  eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) (fun a => (Algebra.commutes u a).symm)

theorem evU_apply (u : ℂ) (p : A[X]) : evU u p = eval₂ (RingHom.id A) (algebraMap ℂ A u) p := rfl

theorem evU_tmPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (k : ℕ) (a b : Fin n) :
    evU u (tmPoly E k a b) = Tm E (u - (k : ℂ)) a b := by
  unfold tmPoly Tm
  split_ifs <;> simp [evU_apply, map_sub]

theorem evU_qdetPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evU u (qdetPoly E) = qdet E u := by
  unfold qdetPoly qdet qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_list_prod, List.map_ofFn]
  congr 1
  · simp
  · congr 1
    congr 1
    funext k
    simp [Function.comp, evU_tmPoly]

theorem natDegree_tmPoly_le {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    (tmPoly E k a b).natDegree ≤ if a = b then 1 else 0 := by
  unfold tmPoly
  split_ifs with h
  · refine (natDegree_add_le _ _).trans ?_
    refine max_le ((natDegree_sub_le _ _).trans (max_le natDegree_X_le ?_)) ?_ <;> simp
  · simp

theorem natDegree_prod_le {n : ℕ} (E : Fin n → Fin n → A) (σ : Equiv.Perm (Fin n)) :
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod.natDegree ≤
      ∑ k : Fin n, if σ k = k then 1 else 0 := by
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_le_sum fun k _ => natDegree_tmPoly_le E k (σ k) k

theorem fixed_add_support {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (∑ k : Fin n, if σ k = k then 1 else 0) + σ.support.card = n := by
  have h : σ.support.card = ∑ k : Fin n, if σ k = k then 0 else 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
  rw [h, ← Finset.sum_add_distrib]
  simp only [apply_ite₂]
  simp

theorem natDegree_prod_ne_one {n : ℕ} (E : Fin n → Fin n → A) {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) :
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod.natDegree + 2 ≤ n := by
  have h1 := natDegree_prod_le E σ
  have h2 := fixed_add_support σ
  have h3 := Equiv.Perm.two_le_card_support_of_ne_one hσ
  omega

omit [Algebra ℂ A] in

theorem prod_linear (m : ℕ) (c : Fin m → A) :
    (List.ofFn fun k : Fin m => X + C (c k)).prod.natDegree ≤ m ∧
      (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff m = 1 ∧
      ∀ j, j + 1 = m → (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff j = ∑ k, c k := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun k => c k.castSucc)
    rw [List.ofFn_succ', List.prod_concat]
    set P := (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod
    refine ⟨?_, ?_, ?_⟩
    · refine (natDegree_mul_le).trans ?_
      have : (X + C (c (Fin.last m))).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
      omega
    · rw [mul_add, coeff_add, coeff_mul_X, coeff_mul_C, h2,
        coeff_eq_zero_of_natDegree_lt (show P.natDegree < m + 1 by omega)]
      simp
    · intro j hj
      have hj' : j = m := by omega
      subst hj'
      rw [Fin.sum_univ_castSucc, mul_add, coeff_add, coeff_mul_C, h2, one_mul]
      congr 1
      cases j with
      | zero => simp [P]
      | succ i => rw [coeff_mul_X, h3 i rfl]

theorem tmPoly_diag {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a : Fin n) :
    tmPoly E k a a = X + C (E a a - algebraMap ℂ A (k : ℂ)) := by
  unfold tmPoly
  simp only [if_true, map_sub]
  abel

theorem sum_fin_cast (n : ℕ) : ∑ k : Fin n, ((k : ℕ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

theorem natDegree_qdetPoly_le {n : ℕ} (E : Fin n → Fin n → A) : (qdetPoly E).natDegree ≤ n := by
  unfold qdetPoly
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le E σ).trans ?_
  have := fixed_add_support σ
  omega

theorem coeff_qdetPoly_top {n : ℕ} (E : Fin n → Fin n → A) (j : ℕ) (hj : n ≤ j + 1) :
    (qdetPoly E).coeff j = (List.ofFn fun k : Fin n => X + C (E k k - algebraMap ℂ A ((k : ℕ) : ℂ))).prod.coeff j := by
  unfold qdetPoly
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n))), coeff_add, finsetSum_coeff]
  rw [Finset.sum_eq_zero]
  · simp [tmPoly_diag]
  · intro σ hσ
    have hσ1 : σ ≠ 1 := Finset.ne_of_mem_erase hσ
    have := natDegree_prod_ne_one E hσ1
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

end Capelli

theorem quantum_determinant_leading_terms : QdetSub := by
  intro A _ _ n Eo hn
  obtain ⟨-, htop, hsub⟩ := prod_linear n fun k => Eo k k - algebraMap ℂ A ((k : ℕ) : ℂ)
  have hN : (qdetPoly Eo).coeff n = 1 := by rw [coeff_qdetPoly_top Eo n (by omega), htop]
  have hN1 : (qdetPoly Eo).coeff (n - 1) = ∑ i, Eo i i - algebraMap ℂ A (((n : ℂ) * ((n : ℂ) - 1)) / 2) := by
    rw [coeff_qdetPoly_top Eo (n - 1) (by omega), hsub (n - 1) (by omega), Finset.sum_sub_distrib,
      ← map_sum, sum_fin_cast]
  refine ⟨fun j => (qdetPoly Eo).coeff j, fun u => ?_⟩
  have hdeg : (qdetPoly Eo).natDegree < n - 1 + 1 + 1 := by
    have := natDegree_qdetPoly_le Eo
    omega
  rw [← evU_qdetPoly Eo u, evU_apply, eval₂_eq_sum_range' _ hdeg, Finset.sum_range_succ,
    Finset.sum_range_succ, show n - 1 + 1 = n by omega, hN, hN1]
  simp only [RingHom.id_apply, one_mul, ← map_pow]
  rw [Finset.sum_congr rfl fun j _ => (Algebra.commutes (u ^ j) ((qdetPoly Eo).coeff j)).symm,
    ← Algebra.commutes (u ^ (n - 1))]
  abel

end

end GroundTheory.BlockD.FourierDecayAlt.GaugeExists
