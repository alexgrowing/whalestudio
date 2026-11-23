import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.DeltaEqGdelta

open MvPolynomial

namespace PI.WickFormula

section lprod
variable {AA : Type} [Ring AA]

def lprod {n : ℕ} (c : Fin n → AA) (e : Fin n → ℕ) : AA := (List.ofFn fun i => c i ^ e i).prod

theorem lprod_succ {n : ℕ} (c : Fin (n + 1) → AA) (e : Fin (n + 1) → ℕ) :
    lprod c e = c 0 ^ e 0 * lprod (fun i => c i.succ) (fun i => e i.succ) := by
  simp only [lprod, List.ofFn_succ, List.prod_cons]

theorem lprod_bump {n : ℕ} (c : Fin n → AA) (hc : ∀ i i', Commute (c i) (c i'))
    (e e' : Fin n → ℕ) (i : Fin n) (h1 : e' i = e i + 1) (h2 : ∀ i', i' ≠ i → e' i' = e i') :
    lprod c e' = c i * lprod c e := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [lprod_succ c e', lprod_succ c e]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · have ht : (fun j : Fin n => e' j.succ) = fun j => e j.succ :=
        funext fun j => h2 _ (Fin.succ_ne_zero j)
      rw [ht, h1, pow_succ', mul_assoc]
    · have h0 : e' 0 = e 0 := h2 0 (Fin.succ_ne_zero j).symm
      have key := ih (fun i => c i.succ) (fun a b => hc _ _) (fun j => e j.succ) (fun j => e' j.succ) j h1
        (fun i' hi' => h2 _ (fun h => hi' (Fin.succ_injective _ h)))
      rw [h0, key]
      simp only [← mul_assoc, ((hc 0 j.succ).pow_left (e 0)).eq]

end lprod

section ord
variable {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA] {r s : ℕ}

def omon (a : Fin r → AA) (a' : Fin s → AA) (m : Fin r ⊕ Fin s →₀ ℕ) : AA :=
  lprod a (fun i => m (Sum.inl i)) * lprod a' (fun j => m (Sum.inr j))

theorem ordEval_eq (a : Fin r → AA) (a' : Fin s → AA) (P : MvPolynomial (Fin r ⊕ Fin s) k) :
    ordEval a a' P = ∑ m ∈ P.support, P.coeff m • omon a a' m := rfl

theorem ordEval_eq_sum_of (a : Fin r → AA) (a' : Fin s → AA) (P : MvPolynomial (Fin r ⊕ Fin s) k)
    (t : Finset (Fin r ⊕ Fin s →₀ ℕ)) (ht : P.support ⊆ t) :
    ordEval a a' P = ∑ m ∈ t, P.coeff m • omon a a' m := by
  rw [ordEval_eq]
  refine Finset.sum_subset ht fun m _ hm => ?_
  have h0 : P.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [h0, zero_smul]

theorem ordEval_add (a : Fin r → AA) (a' : Fin s → AA) (P Q : MvPolynomial (Fin r ⊕ Fin s) k) :
    ordEval a a' (P + Q) = ordEval a a' P + ordEval a a' Q := by
  rw [ordEval_eq_sum_of a a' (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    ordEval_eq_sum_of a a' P _ (fun x hx => Finset.mem_union_left _ hx),
    ordEval_eq_sum_of a a' Q _ (fun x hx => Finset.mem_union_right _ hx), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, add_smul]

theorem ordEval_smul (a : Fin r → AA) (a' : Fin s → AA) (c : k) (P : MvPolynomial (Fin r ⊕ Fin s) k) :
    ordEval a a' (c • P) = c • ordEval a a' P := by
  rw [ordEval_eq_sum_of a a' (c • P) P.support MvPolynomial.support_smul, ordEval_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul]

noncomputable def ordL (k : Type) [CommRing k] [Algebra k AA] (a : Fin r → AA) (a' : Fin s → AA) :
    MvPolynomial (Fin r ⊕ Fin s) k →ₗ[k] AA where
  toFun := ordEval a a'
  map_add' := ordEval_add a a'
  map_smul' := ordEval_smul a a'

theorem ordEval_monomial (a : Fin r → AA) (a' : Fin s → AA) (m : Fin r ⊕ Fin s →₀ ℕ) (c : k) :
    ordEval a a' (monomial m c) = c • omon a a' m := by
  rw [ordEval_eq_sum_of a a' _ {m} MvPolynomial.support_monomial_subset]
  simp [MvPolynomial.coeff_monomial]

end ord

theorem ordLin_holds : OrdLin := by
  intro k AA _ _ _ r s a a'
  exact ⟨ordL k a a', fun P => rfl⟩

theorem ordX_holds : OrdX := by
  intro k AA _ _ _ r s a a' ha i R
  refine MvPolynomial.induction_on' R (fun m c => ?_) (fun p q hp hq => ?_)
  · have hX : (X (Sum.inl i) : MvPolynomial (Fin r ⊕ Fin s) k) * monomial m c
        = monomial (m + Finsupp.single (Sum.inl i) 1) c := by
      rw [X, monomial_mul, one_mul, add_comm]
    rw [hX, ordEval_monomial, ordEval_monomial, mul_smul_comm]
    congr 1
    unfold omon
    have hb := lprod_bump a ha (fun j => m (Sum.inl j))
      (fun j => (m + Finsupp.single (Sum.inl i) 1 : Fin r ⊕ Fin s →₀ ℕ) (Sum.inl j)) i
      (by simp) (fun i' hi' => by simp [Finsupp.single_apply, Ne.symm hi'])
    rw [hb, mul_assoc]
    simp [Finsupp.single_apply]
  · rw [mul_add, ordEval_add, ordEval_add, hp, hq, mul_add]

end PI.WickFormula
