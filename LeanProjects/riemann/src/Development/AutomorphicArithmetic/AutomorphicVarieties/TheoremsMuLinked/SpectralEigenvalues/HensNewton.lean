import Mathlib
open IsLocalRing Polynomial
open scoped Ring

private theorem hens_newton {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (f : R[X]) (h₁ : f.eval 0 ∈ maximalIdeal R) (h₂ : IsUnit (f.derivative.eval 0)) :
    ∃ a : R, f.eval a = 0 ∧ a ∈ maximalIdeal R := by
  classical
  set I := maximalIdeal R with hI
  let c : ℕ → R := fun n => Nat.recOn n 0 fun _ b => b - f.eval b * (f.derivative.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f.derivative.eval (c n))⁻¹ʳ := fun n => rfl
  have hev : ∀ (g : R[X]) (b : R), b ∈ I → g.eval b - g.eval 0 ∈ I := by
    intro g b hb
    obtain ⟨t, ht⟩ := sub_dvd_eval_sub b 0 g
    rw [ht, sub_zero]
    exact I.mul_mem_right _ hb
  have hcI : ∀ n, c n ∈ I := by
    intro n
    induction n with
    | zero => exact I.zero_mem
    | succ n ih =>
      rw [hc]
      refine I.sub_mem ih (I.mul_mem_right _ ?_)
      have := I.add_mem (hev f _ ih) h₁
      simpa using this
  have hu : ∀ n, IsUnit (f.derivative.eval (c n)) := by
    intro n
    by_contra hn
    have h3 : f.derivative.eval (c n) ∈ I := (mem_maximalIdeal _).2 hn
    have h4 := I.sub_mem h3 (hev f.derivative _ (hcI n))
    rw [sub_sub_cancel] at h4
    exact (mem_maximalIdeal _).1 h4 h₂
  have hf : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa [c] using h₁
    | succ n ih =>
      obtain ⟨k, hk⟩ := binomExpansion f (c n) (-(f.eval (c n) * (f.derivative.eval (c n))⁻¹ʳ))
      rw [hc, sub_eq_add_neg, hk]
      have h5 : f.eval (c n) + f.derivative.eval (c n) * -(f.eval (c n) * (f.derivative.eval (c n))⁻¹ʳ) = 0 := by
        rw [mul_neg, mul_left_comm, Ring.mul_inverse_cancel _ (hu n), mul_one, add_neg_cancel]
      rw [h5, zero_add]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (show n + 1 + 1 ≤ (n + 1) * 2 by omega) ?_)
      rw [pow_mul]
      exact Ideal.pow_mem_pow (neg_mem (Ideal.mul_mem_right _ _ ih)) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [SModEq.sub_mem] at ih ⊢
      have h6 : f.eval (c k) * (f.derivative.eval (c k))⁻¹ʳ ∈ I ^ m :=
        Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) (hf k))
      have := (I ^ m).add_mem ih h6
      rw [hc]
      convert this using 1
      ring
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hf _)
  · specialize ha 1
    rw [pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem] at ha
    have := I.sub_mem (hcI 1) ha
    simpa using this

private theorem hens_one {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (P : R[X]) (a e w q u : R) (hq : q ∈ maximalIdeal R) (hu : IsUnit u)
    (h0 : P.eval a = e ^ 2 * w * q) (h1 : P.derivative.eval a = e * u) :
    ∃ y ∈ maximalIdeal R, P.eval (a + e * w * y) = 0 := by
  set T := taylor a P with hT
  set S := T.divX.divX with hS
  have hdec : T = C (P.eval a) + C (P.derivative.eval a) * X + X ^ 2 * S := by
    have e1 := T.divX_mul_X_add
    have e2 := T.divX.divX_mul_X_add
    rw [coeff_divX, zero_add, hT, taylor_coeff_one, ← hT, ← hS] at e2
    rw [hT, taylor_coeff_zero, ← hT, ← e2] at e1
    rw [← e1]
    ring
  obtain ⟨y, hy, hym⟩ := hens_newton (C q + C u * X + C w * X ^ 2 * S.comp (C (e * w) * X))
    (by simpa using hq) (by simpa [derivative_mul] using hu)
  refine ⟨y, hym, ?_⟩
  have h2 : P.eval (a + e * w * y) = T.eval (e * w * y) := by
    rw [hT, taylor_eval, add_comm]
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_comp] at hy
  rw [h2, hdec, h0, h1]
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
  linear_combination e ^ 2 * w * hy

private theorem hens_eval {R : Type} [CommRing R] (I : Ideal R) (F : R[X]) (h : ∀ k, F.coeff k ∈ I)
    (a : R) : F.eval a ∈ I := by
  rw [eval_eq_sum_range]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (h k)

theorem UpperTheory.V.Th.Sp.hens :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (n : ℕ) (al : Fin n → O), Function.Injective al → ∀ K : ℕ, ∃ K' : ℕ, ∀ P : O[X], P.Monic → P.natDegree = n → (∀ k, P.coeff k - (∏ i, (X - C (al i))).coeff k ∈ maximalIdeal O ^ K') → ∃ α : Fin n → O, P = ∏ i, (X - C (α i)) ∧ ∀ i, α i - al i ∈ maximalIdeal O ^ K := by
  intro O _ _ _ _ n al hal K
  classical
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm : maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  have hpm : p ∈ maximalIdeal O := by rw [hm]; exact Ideal.mem_span_singleton_self p
  set e : Fin n → O := fun i => ∏ k ∈ Finset.univ.erase i, (al i - al k) with he
  have he0 : ∀ i, e i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun k hk => sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hk) (hal h).symm
  have hN : ∀ i, ∃ N : ℕ, ∀ z ∈ maximalIdeal O ^ N, e i ^ 2 * p ^ K * p ∣ z := by
    intro i
    obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (he0 i)) (pow_ne_zero K hp.ne_zero)) hp.ne_zero) hp
    refine ⟨N, fun z hz => ?_⟩
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
    exact hN.dvd.trans hz
  choose N hN using hN
  refine ⟨Finset.univ.sup N, fun P hP hdeg hco => ?_⟩
  have hroot : ∀ i, ∃ y ∈ maximalIdeal O, P.eval (al i + e i * p ^ K * y) = 0 := by
    intro i
    have hle : maximalIdeal O ^ (Finset.univ.sup N) ≤ maximalIdeal O ^ N i :=
      Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i))
    have hG : (∏ j, (X - C (al j)) : O[X]) = (X - C (al i)) * ∏ j ∈ Finset.univ.erase i, (X - C (al j)) :=
      (Finset.mul_prod_erase _ (fun j => (X - C (al j) : O[X])) (Finset.mem_univ i)).symm
    have hF : ∀ k, (P - ∏ j, (X - C (al j))).coeff k ∈ maximalIdeal O ^ N i := fun k => by
      rw [coeff_sub]; exact hle (hco k)
    have hF' : ∀ k, (derivative (P - ∏ j, (X - C (al j)))).coeff k ∈ maximalIdeal O ^ N i := fun k => by
      rw [coeff_derivative]; exact Ideal.mul_mem_right _ _ (hF _)
    obtain ⟨s, hs⟩ := hN i _ (hens_eval _ _ hF (al i))
    obtain ⟨t, ht⟩ := hN i _ (hens_eval _ _ hF' (al i))
    rw [hG] at hs ht
    simp only [eval_sub, eval_mul, eval_X, eval_C, sub_self, zero_mul, sub_zero] at hs
    simp only [derivative_sub, derivative_mul, derivative_X, derivative_C, eval_sub, eval_add,
      eval_mul, eval_X, eval_C, sub_self, zero_mul, sub_zero, one_mul, add_zero, eval_prod] at ht
    refine hens_one P (al i) (e i) (p ^ K) (p * s) (1 + p * (e i * p ^ K * t))
      (Ideal.mul_mem_right _ _ hpm) ?_ (by rw [hs]; ring) ?_
    · by_contra hn
      have h3 := (maximalIdeal O).sub_mem ((mem_maximalIdeal _).2 hn)
        (Ideal.mul_mem_right (e i * p ^ K * t) _ hpm)
      rw [add_sub_cancel_right] at h3
      exact (mem_maximalIdeal _).1 h3 isUnit_one
    · have ht' : P.derivative.eval (al i) - e i = e i ^ 2 * p ^ K * p * t := ht
      linear_combination ht'
  choose y hy hy0 using hroot
  have hinj : Function.Injective fun i => al i + e i * p ^ K * y i := by
    intro i j hij
    by_contra hne
    obtain ⟨a, ha⟩ : al i - al j ∣ e i :=
      Finset.dvd_prod_of_mem (fun k => al i - al k) (Finset.mem_erase.2 ⟨Ne.symm hne, Finset.mem_univ _⟩)
    obtain ⟨b, hb⟩ : al j - al i ∣ e j :=
      Finset.dvd_prod_of_mem (fun k => al j - al k) (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)
    have hij' : al i + e i * p ^ K * y i = al j + e j * p ^ K * y j := hij
    rw [ha, hb] at hij'
    have h1 : (al i - al j) * (1 - (-(a * p ^ K * y i) - b * p ^ K * y j)) = 0 := by
      linear_combination hij'
    have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 fun h => hne (hal h)))
    have h3 : (1 : O) ∈ maximalIdeal O := by
      rw [h2]
      exact sub_mem (neg_mem (Ideal.mul_mem_left _ _ (hy i))) (Ideal.mul_mem_left _ _ (hy j))
    exact (mem_maximalIdeal _).1 h3 isUnit_one
  refine ⟨fun i => al i + e i * p ^ K * y i, ?_, fun i => ?_⟩
  · have hGm : (∏ i, (X - C (al i + e i * p ^ K * y i)) : O[X]).Monic :=
      monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
    have hGd : (∏ i, (X - C (al i + e i * p ^ K * y i)) : O[X]).natDegree = n := by
      rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
      simp only [natDegree_X_sub_C]
      simp
    refine eq_of_degree_le_of_eval_index_eq Finset.univ hinj.injOn ?_ ?_ ?_ ?_
    · rw [degree_eq_natDegree hP.ne_zero, hdeg]; simp
    · rw [degree_eq_natDegree hP.ne_zero, degree_eq_natDegree hGm.ne_zero, hdeg, hGd]
    · rw [hP.leadingCoeff, hGm.leadingCoeff]
    · intro i _
      rw [hy0 i, eval_prod]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp)).symm
  · rw [add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hpm K))
