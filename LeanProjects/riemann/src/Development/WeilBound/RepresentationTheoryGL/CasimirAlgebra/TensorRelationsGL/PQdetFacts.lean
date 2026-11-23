import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.QdetFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.RowCol
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Central

noncomputable section

open Polynomial Formalism.REAL

namespace PositivityTheory.Rg.Cz

namespace QF

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem qdet_eq_capelliC {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) : qdet E x = capelliC E x := by
  simp only [qdet, capelliC, cminor, qminor, Tm, capEntry, id]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [zsmul_eq_mul]
  congr 3
  funext k
  rw [add_comm]

theorem capelliC_negT {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) :
    capelliC (fun a b => -E b a) x = (-1) ^ n * rminor E id id ((n : ℂ) - 1 - x) := by
  simp only [capelliC, cminor, rminor, id]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h : (List.ofFn fun j : Fin n => capEntry (fun a b => -E b a) (x - ((j : ℕ) : ℂ)) (σ j) j) =
      (List.ofFn fun j : Fin n => capEntry E ((n : ℂ) - 1 - x - (n : ℂ) + 1 + ((j : ℕ) : ℂ)) j (σ j)).map Neg.neg := by
    rw [List.map_ofFn]
    congr 1
    funext j
    simp only [Function.comp, capEntry]
    by_cases hj : σ j = j
    · rw [if_pos hj, if_pos hj.symm, neg_add, ← map_neg]
      congr 2
      ring
    · rw [if_neg hj, if_neg (Ne.symm hj), neg_add, neg_zero]
  rw [h, List.prod_map_neg, List.length_ofFn, zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc,
    ((Commute.neg_one_left _).pow_left n).eq]

theorem qdet_negT {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ) :
    qdet (fun a b => -E b a) u = (-1) ^ n * qdet E ((n : ℂ) - 1 - u) := by
  rw [qdet_eq_capelliC, capelliC_negT, qdet_eq_capelliC, capelliC, cminor_eq_rminor E hE]

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
  rw [evU_apply, tmPoly, Tm]
  split_ifs <;> simp [eval₂_add, eval₂_sub, map_sub]

theorem evU_qdetPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evU u (qdetPoly E) = qdet E u := by
  simp only [qdetPoly, qdet, qminor, id, map_sum, map_mul, map_list_prod, List.map_ofFn, Function.comp_def,
    evU_tmPoly]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [evU_apply, eval₂_C]
  rfl

theorem natDegree_tmPoly_le {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    (tmPoly E k a b).natDegree ≤ if a = b then 1 else 0 := by
  rw [tmPoly]
  split_ifs with h
  · exact (natDegree_add_le _ _).trans (max_le (natDegree_X_sub_C_le _) (by rw [natDegree_C]; exact zero_le_one))
  · rw [zero_add, natDegree_C]

theorem natDegree_prod_le {n : ℕ} (E : Fin n → Fin n → A) (σ : Equiv.Perm (Fin n)) :
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod.natDegree ≤
      ∑ k : Fin n, if σ k = k then 1 else 0 := by
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_le_sum fun k _ => natDegree_tmPoly_le E k (σ k) k

theorem fixed_add_support {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (∑ k : Fin n, if σ k = k then 1 else 0) + σ.support.card = n := by
  rw [Finset.sum_boole, Nat.cast_id]
  have hs : σ.support = Finset.univ.filter (fun k => ¬ σ k = k) := by
    ext k
    simp [Equiv.Perm.mem_support]
  rw [hs, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

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
  | zero =>
    refine ⟨by simp, by simp, fun j hj => by omega⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun k => c k.castSucc)
    have e : (List.ofFn fun k : Fin (m + 1) => X + C (c k)).prod =
        (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod * (X + C (c (Fin.last m))) := by
      rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
    rw [e]
    have hP : (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod.coeff (m + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    refine ⟨?_, ?_, ?_⟩
    · refine natDegree_mul_le.trans (add_le_add h1 ?_)
      exact (natDegree_add_le _ _).trans (max_le natDegree_X_le (by rw [natDegree_C]; exact zero_le_one))
    · rw [mul_add, coeff_add, coeff_mul_C, coeff_mul_X, h2, hP, zero_mul, add_zero]
    · intro j hj
      obtain rfl : j = m := by omega
      rw [Fin.sum_univ_castSucc, mul_add, coeff_add, coeff_mul_C, h2, one_mul]
      congr 1
      rcases j with _ | j
      · simp
      · rw [coeff_mul_X]
        exact h3 j rfl

theorem tmPoly_diag {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a : Fin n) :
    tmPoly E k a a = X + C (E a a - algebraMap ℂ A (k : ℂ)) := by
  rw [tmPoly, if_pos rfl, C_sub]
  abel

theorem sum_fin_cast (n : ℕ) : ∑ k : Fin n, ((k : ℕ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℂ)) n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem natDegree_qdetPoly_le {n : ℕ} (E : Fin n → Fin n → A) : (qdetPoly E).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le E σ).trans ?_)
  have := fixed_add_support σ
  omega

theorem coeff_qdetPoly_top {n : ℕ} (E : Fin n → Fin n → A) (j : ℕ) (hj : n ≤ j + 1) :
    (qdetPoly E).coeff j = (List.ofFn fun k : Fin n => X + C (E k k - algebraMap ℂ A ((k : ℕ) : ℂ))).prod.coeff j := by
  rw [qdetPoly, finset_sum_coeff, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, C_1, one_mul, Equiv.Perm.one_apply, tmPoly_diag]
  · intro σ _ hσ
    rw [coeff_C_mul]
    have := natDegree_prod_ne_one E hσ
    rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Alg

section Op

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem coeff_eq_zero_of_evU (r : (Module.End ℂ M)[X]) (h : ∀ u : ℂ, evU u r = 0) (i : ℕ) : r.coeff i = 0 := by
  by_cases hi : i ∈ r.support
  swap
  · exact notMem_support_iff.mp hi
  ext m
  rw [LinearMap.zero_apply]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  have hq0 : (∑ e ∈ r.support, monomial e (φ (r.coeff e m))) = 0 := by
    refine Polynomial.funext fun u => ?_
    rw [eval_zero, eval_finset_sum]
    have hu := congrArg (fun T : Module.End ℂ M => φ (T m)) (h u)
    simp only [evU_apply, eval₂_eq_sum, Polynomial.sum_def, LinearMap.zero_apply, map_zero, RingHom.id_apply,
      LinearMap.sum_apply, Module.End.mul_apply, ← map_pow, Module.algebraMap_end_apply,
      map_smul, map_sum, smul_eq_mul] at hu
    rw [← hu]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [eval_monomial, mul_comm]
  have hc := congrArg (fun p : ℂ[X] => p.coeff i) hq0
  simp only [finset_sum_coeff, coeff_monomial, coeff_zero, Finset.sum_ite_eq', if_pos hi] at hc
  exact hc

end Op

end QF

open QF ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

theorem qdetFacts_holds : QdetFacts := by
  intro n M _ _ E hE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u a b
    rw [qdet_eq_capelliC]
    exact (capelliC_central E hE u a b).symm
  · refine ⟨fun i => (qdetPoly E).coeff i, fun u => ?_⟩
    rw [← evU_qdetPoly, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le E))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  · intro l hl
    have key : ∀ i, (qdetPoly E).coeff i =
        algebraMap ℂ (Module.End ℂ M) ((∏ k : Fin n, (X + C (l k))).coeff i) := by
      intro i
      rw [← coeff_map, ← sub_eq_zero, ← coeff_sub]
      refine coeff_eq_zero_of_evU _ (fun u => ?_) i
      rw [map_sub, evU_qdetPoly, hl u, evU_apply, eval₂_map, RingHom.id_comp, eval₂_at_apply, eval_prod]
      simp only [eval_add, eval_X, eval_C, sub_self]
    cases n with
    | zero => simp
    | succ m =>
      have h1 := key m
      have h2 := (prod_linear (m + 1) fun k => E k k - algebraMap ℂ (Module.End ℂ M) ((k : ℕ) : ℂ)).2.2 m rfl
      have h3 := (prod_linear (m + 1) l).2.2 m rfl
      rw [List.prod_ofFn] at h3
      rw [coeff_qdetPoly_top E m le_rfl, h2, h3, Finset.sum_sub_distrib, sub_eq_iff_eq_add, ← map_sum] at h1
      rw [h1, ← map_add, sum_fin_cast]
  · unfold GlRel
    intro a b c d
    have h := hE d c b a
    simp only [@eq_comm _ c b, @eq_comm _ a d] at h
    simp only [neg_mul_neg]
    rw [← neg_sub, h]
    split_ifs <;> abel
  · intro l hl u
    rw [qdet_negT E hE, hl]
    have hp : ∏ k : Fin n, (u + (-((n : ℂ) - 1) - l k)) = (-1) ^ n * ∏ k : Fin n, ((n : ℂ) - 1 - u + l k) := by
      rw [show (-1 : ℂ) ^ n = ∏ _k : Fin n, (-1 : ℂ) by simp, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by ring
    rw [hp, map_mul, map_pow, map_neg, map_one]

end PositivityTheory.Rg.Cz

end
