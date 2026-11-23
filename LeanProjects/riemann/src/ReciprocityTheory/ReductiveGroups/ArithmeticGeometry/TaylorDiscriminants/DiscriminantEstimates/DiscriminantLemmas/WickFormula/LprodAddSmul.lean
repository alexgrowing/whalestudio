import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.OrdEvalEqSumOf

open MvPolynomial

namespace PI.WickFormula

section gen
variable {AA : Type} [Ring AA]

theorem lprod_of_zero {n : ℕ} (c : Fin n → AA) (e : Fin n → ℕ) (h : ∀ i, e i = 0) : lprod c e = 1 := by
  unfold lprod
  simp [h]

theorem add_pow_smul {M : Type} [AddCommGroup M] [Module AA M] (x y : AA) (w : M)
    (hxy : Commute y x) (hw : y • w = 0) (n : ℕ) : (x + y) ^ n • w = x ^ n • w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    have hyx : y • (x • w) = 0 := by rw [← mul_smul, hxy.eq, mul_smul, hw, smul_zero]
    rw [pow_succ, mul_smul, add_smul, hw, add_zero, ih (x • w) hyx, ← mul_smul, ← pow_succ]

theorem lprod_add_smul {M : Type} [AddCommGroup M] [Module AA M] {n : ℕ} (x y : Fin n → AA)
    (e : Fin n → ℕ) (v : M) (hxy : ∀ i j, Commute (y i) (x j)) (hy : ∀ i, y i • v = 0) :
    lprod (x + y) e • v = lprod x e • v := by
  induction n with
  | zero => simp [lprod]
  | succ n ih =>
    have key : ∀ (c : Fin (n + 1) → AA), lprod c e = c 0 ^ e 0 * lprod (fun i => c i.succ) (fun i => e i.succ) := by
      intro c; simp [lprod, List.ofFn_succ]
    have ih' : lprod (fun i => (x + y) i.succ) (fun i => e i.succ) • v =
        lprod (fun i => x i.succ) (fun i => e i.succ) • v :=
      ih (fun i => x i.succ) (fun i => y i.succ) (fun i => e i.succ) (fun i j => hxy _ _) (fun i => hy _)
    rw [key, key, mul_smul, mul_smul, ih', Pi.add_apply]
    apply add_pow_smul _ _ _ (hxy 0 0)
    have hcm : Commute (y 0) (lprod (fun i => x i.succ) (fun i => e i.succ)) := by
      unfold lprod
      apply Commute.list_prod_right
      intro z hz
      rw [List.mem_ofFn] at hz
      obtain ⟨i, rfl⟩ := hz
      exact (hxy 0 i.succ).pow_right _
    rw [← mul_smul, hcm.eq, mul_smul, hy, smul_zero]

end gen

section comm
variable {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA]

theorem comm_pow_succ (b c : AA) (t : k) (h : b * c = c * b + algebraMap k AA t) (n : ℕ) :
    b * c ^ (n + 1) = c ^ (n + 1) * b + (((n : k) + 1) * t) • c ^ n := by
  induction n with
  | zero => simp [h, Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    calc b * c ^ (n + 1 + 1) = (b * c ^ (n + 1)) * c := by rw [pow_succ c (n + 1), mul_assoc]
      _ = (c ^ (n + 1) * b + (((n : k) + 1) * t) • c ^ n) * c := by rw [ih]
      _ = c ^ (n + 1) * (b * c) + (((n : k) + 1) * t) • (c ^ n * c) := by
          rw [add_mul, mul_assoc, smul_mul_assoc]
      _ = c ^ (n + 1) * (c * b + algebraMap k AA t) + (((n : k) + 1) * t) • c ^ (n + 1) := by
          rw [h, ← pow_succ]
      _ = c ^ (n + 1 + 1) * b + t • c ^ (n + 1) + (((n : k) + 1) * t) • c ^ (n + 1) := by
          rw [mul_add, ← mul_assoc, ← pow_succ, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
      _ = c ^ (n + 1 + 1) * b + ((((n + 1 : ℕ) : k) + 1) * t) • c ^ (n + 1) := by
          rw [add_assoc, ← add_smul]
          congr 2
          push_cast
          ring

theorem comm_pow (b c : AA) (t : k) (h : b * c = c * b + algebraMap k AA t) (n : ℕ) :
    b * c ^ n = c ^ n * b + ((n : k) * t) • c ^ (n - 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [comm_pow_succ b c t h m]
    simp

theorem lprod_comm {n : ℕ} (c : Fin n → AA) (hc : ∀ i i', Commute (c i) (c i')) (b : AA) (t : Fin n → k)
    (h : ∀ j, b * c j = c j * b + algebraMap k AA (t j)) (e : Fin n → ℕ) :
    b * lprod c e = lprod c e * b +
      ∑ j, ((e j : k) * t j) • lprod c (fun j' => e j' - if j = j' then 1 else 0) := by
  induction n with
  | zero => simp [lprod]
  | succ n ih =>
    have key : ∀ (e : Fin (n + 1) → ℕ), lprod c e = c 0 ^ e 0 * lprod (fun i => c i.succ) (fun i => e i.succ) := by
      intro e; simp [lprod, List.ofFn_succ]
    have ih' := ih (fun i => c i.succ) (fun i i' => hc _ _) (fun i => t i.succ) (fun j => h j.succ)
      (fun i => e i.succ)
    rw [key, ← mul_assoc, comm_pow b (c 0) (t 0) (h 0) (e 0), add_mul, mul_assoc, ih', Fin.sum_univ_succ]
    simp only [key, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, Fin.succ_inj, if_true, if_false, tsub_zero,
      mul_add, Finset.mul_sum, mul_smul_comm, smul_mul_assoc, ← mul_assoc, ite_true, ite_false]
    abel

end comm

theorem base_holds : Base := by
  intro k AA M _ _ _ _ _ r s a b a' b' κ σ₀ H Q hQ
  unfold ordEval
  rw [Finset.sum_smul, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro m hm
  have key : (lprod (a + b) (fun i => m (Sum.inl i)) * lprod (a' + b') (fun j => m (Sum.inr j))) • σ₀ =
      (lprod a (fun i => m (Sum.inl i)) * lprod a' (fun j => m (Sum.inr j))) • σ₀ := by
    rw [lprod_of_zero _ _ (fun i => hQ m hm i), lprod_of_zero _ _ (fun i => hQ m hm i), one_mul, one_mul]
    exact lprod_add_smul a' b' _ σ₀ (fun i j => (H.h2 j i).2.1.symm) H.h6
  simp only [lprod] at key
  simp only [mul_smul] at key
  simp only [Algebra.smul_def, mul_smul]
  rw [key]

theorem omon_lower {AA : Type} [Ring AA] {r s : ℕ} (a : Fin r → AA) (a' : Fin s → AA)
    (m : Fin r ⊕ Fin s →₀ ℕ) (j : Fin s) :
    omon a a' (m - Finsupp.single (Sum.inr j) 1) =
      lprod a (fun i => m (Sum.inl i)) * lprod a' (fun j' => m (Sum.inr j') - if j = j' then 1 else 0) := by
  unfold omon
  congr 1
  · congr 1
    funext i
    simp
  · congr 1
    funext j'
    simp [Finsupp.single_apply]

theorem b_mul_ordEval {k AA M : Type} [CommRing k] [Ring AA] [Algebra k AA] [AddCommGroup M] [Module AA M]
    {r s : ℕ} {a b : Fin r → AA} {a' b' : Fin s → AA} {κ : Fin r → Fin s → k} {σ₀ : M}
    (H : Hyp a b a' b' κ σ₀) (i : Fin r) (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    b i * ordEval (a + b) (a' + b') R =
      ordEval (a + b) (a' + b') R * b i + ordEval (a + b) (a' + b') (Gen.dL κ i R) := by
  have hcb : ∀ i', Commute (b i) ((a + b) i') := fun i' => by
    simp only [Pi.add_apply]
    exact Commute.add_right (H.h1 i' i).2.1.symm (H.h1 i i').2.2
  have hC : ∀ j j', Commute ((a' + b') j) ((a' + b') j') := fun j j' => by
    simp only [Pi.add_apply]
    exact Commute.add_left (Commute.add_right (H.h2 j j').1 (H.h2 j j').2.1)
      (Commute.add_right (H.h2 j' j).2.1.symm (H.h2 j j').2.2)
  have hbc : ∀ j, b i * (a' + b') j = (a' + b') j * b i + algebraMap k AA (κ i j) := fun j => by
    simp only [Pi.add_apply]
    have h4 := H.h4 i j
    rw [sub_eq_iff_eq_add] at h4
    rw [mul_add, add_mul, (H.h3 i j).eq, h4]
    abel
  have hA : ∀ e : Fin r → ℕ, Commute (b i) (lprod (a + b) e) := fun e => by
    unfold lprod
    apply Commute.list_prod_right
    intro z hz
    rw [List.mem_ofFn] at hz
    obtain ⟨i', rfl⟩ := hz
    exact (hcb i').pow_right _
  let E : MvPolynomial (Fin r ⊕ Fin s) k →+ AA :=
    AddMonoidHom.mk' (ordEval (a + b) (a' + b')) (ordEval_add _ _)
  induction R using MvPolynomial.induction_on' with
  | monomial m c =>
    have hdl : Gen.dL κ i (monomial m c) =
        ∑ j, κ i j • monomial (m - Finsupp.single (Sum.inr j) 1) (c * (m (Sum.inr j) : k)) := by
      simp [Gen.dL, MvPolynomial.pderiv_monomial]
    have hsum : ordEval (a + b) (a' + b')
        (∑ j, κ i j • monomial (m - Finsupp.single (Sum.inr j) 1) (c * (m (Sum.inr j) : k))) =
        ∑ j, κ i j • ((c * (m (Sum.inr j) : k)) •
          omon (a + b) (a' + b') (m - Finsupp.single (Sum.inr j) 1)) := by
      change E _ = _
      rw [map_sum]
      simp only [E, AddMonoidHom.mk'_apply, ordEval_smul, ordEval_monomial]
    rw [hdl, hsum, ordEval_monomial]
    simp only [omon_lower]
    unfold omon
    rw [mul_smul_comm, ← mul_assoc, (hA _).eq, mul_assoc, lprod_comm (a' + b') hC (b i) (κ i) hbc,
      mul_add, smul_add, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, mul_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_smul_comm, smul_smul, smul_smul]
    congr 1
    ring
  | add P Q hP hQ =>
    rw [ordEval_add, mul_add, hP, hQ, map_add, ordEval_add, add_mul]
    abel

theorem bComm_holds : BComm := by
  intro k AA M _ _ _ _ _ r s a b a' b' κ σ₀ H i R
  rw [← mul_smul, b_mul_ordEval H i R, add_smul, mul_smul, H.h5 i, smul_zero, zero_add]

end PI.WickFormula
