import Formalism.PeriodIntegrals.ContractionsCovariantIff

open Matrix Finset

namespace PI.QnCovLinW

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem ofFn_prod_sum {A : Type*} [Semiring A] {ι : Type*} [Fintype ι] :
    ∀ (t : ℕ) (f : Fin t → ι → A),
      (List.ofFn fun k => ∑ i, f k i).prod = ∑ c : Fin t → ι, (List.ofFn fun k => f k (c k)).prod
  | 0, f => by simp
  | t + 1, f => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ofFn_prod_sum t (fun k => f k.succ), Finset.sum_mul_sum,
      ← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
    simp [Fin.consEquiv]

theorem ofFn_prod_smul {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (t : ℕ) (r : Fin t → ℂ) (x : Fin t → A),
      (List.ofFn fun k => r k • x k).prod = (∏ k, r k) • (List.ofFn x).prod
  | 0, r, x => by simp
  | t + 1, r, x => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ofFn_prod_smul t (fun k => r k.succ) (fun k => x k.succ), Fin.prod_univ_succ,
      smul_mul_smul_comm]

theorem tm_conj {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (u : ℂ) (a b : Fin n) :
    Tm (Econj E P Q) u a b = ∑ x : Fin n × Fin n, (P x.1 a * Q b x.2) • Tm E u x.1 x.2 := by
  have hQP : ∑ c, P c a * Q b c = if a = b then 1 else 0 := by
    have h1 := congrFun (congrFun h b) a
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    rw [show (∑ c, P c a * Q b c) = ∑ c, Q b c * P c a from Finset.sum_congr rfl fun c _ => mul_comm _ _, h1]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  simp only [Tm, Econj, smul_add, Finset.sum_add_distrib, Fintype.sum_prod_type, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_smul, hQP]
  split_ifs <;> simp

theorem qnCovLin : PI.QnCovLin := by
  intro A _ _ n t E P Q hQP a b u
  have key : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun k : Fin t => Tm (Econj E P Q) (u - (k : ℂ)) (a (σ k)) (b k)).prod =
        ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n,
          ((∏ k, P (c k) (a (σ k))) * ∏ k, Q (b k) (d k)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (c k) (d k)).prod := by
    intro σ
    simp only [tm_conj E P Q hQP]
    rw [ofFn_prod_sum]
    have hs : ∀ c : Fin t → Fin n × Fin n,
        (List.ofFn fun k => (P (c k).1 (a (σ k)) * Q (b k) (c k).2) • Tm E (u - (k : ℂ)) (c k).1 (c k).2).prod =
        (fun p : (Fin t → Fin n) × (Fin t → Fin n) => ((∏ k, P (p.1 k) (a (σ k))) * ∏ k, Q (b k) (p.2 k)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (p.1 k) (p.2 k)).prod)
          (Equiv.arrowProdEquivProdArrow (Fin t) (fun _ => Fin n) (fun _ => Fin n) c) := by
      intro c
      rw [ofFn_prod_smul, Finset.prod_mul_distrib]
      rfl
    rw [Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin t) (fun _ => Fin n) (fun _ => Fin n)) _
      (fun p : (Fin t → Fin n) × (Fin t → Fin n) => ((∏ k, P (p.1 k) (a (σ k))) * ∏ k, Q (b k) (p.2 k)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (p.1 k) (p.2 k)).prod) hs,
      Fintype.sum_prod_type]
  have reidx : ∀ σ : Equiv.Perm (Fin t),
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((Equiv.Perm.sign σ : ℤ) : A) *
        (((∏ k, P (c k) (a (σ k))) * ∏ k, Q (b k) (d k)) •
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (c k) (d k)).prod) =
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((∏ k, P (c k) (a k)) * ∏ k, Q (b k) (d k)) •
        (((Equiv.Perm.sign σ : ℤ) : A) *
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (c (σ k)) (d k)).prod) := by
    intro σ
    rw [← (Equiv.arrowCongr σ.symm (Equiv.refl (Fin n))).sum_comp]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, Equiv.symm_symm, id]
    have hp : ∏ k, P (c (σ k)) (a (σ k)) = ∏ k, P (c k) (a k) := Equiv.prod_comp σ (fun k => P (c k) (a k))
    rw [mul_smul_comm, hp]
  simp only [qminor, key, Finset.mul_sum]
  simp only [reidx, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

end PI.QnCovLinW
