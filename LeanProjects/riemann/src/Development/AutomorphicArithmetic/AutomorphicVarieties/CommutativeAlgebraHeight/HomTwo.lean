import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPoly

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem hom_two {n : ℕ} {A : Type} [CommRing A] (P : MvPolynomial (Fin 2) A) (hP : P.IsHomogeneous n) :
    ∃ c : ℕ → A, ∀ (S : Type) [CommRing S] [Algebra A S] (s t : S),
      MvPolynomial.aeval ![s, t] P = ∑ i ∈ Finset.range (n + 1), algebraMap A S (c i) * s ^ (n - i) * t ^ i := by
  classical
  have hd : ∀ d ∈ P.support, d 0 + d 1 = n := fun d hd => by
    have h := hP (MvPolynomial.mem_support_iff.1 hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa [Fin.sum_univ_two] using h
  refine ⟨fun i => ∑ d ∈ P.support with d 1 = i, P.coeff d, fun S _ _ s t => ?_⟩
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    ← Finset.sum_fiberwise_of_maps_to (t := Finset.range (n + 1)) (g := fun d => d 1)
      (fun d h => by have := hd d h; simp only [Finset.mem_range]; omega)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d h => ?_
  rw [Finset.mem_filter] at h
  have h0 : d 0 = n - i := by have := hd d h.1; have := h.2; omega
  simp [Fin.prod_univ_two, h0, h.2, mul_assoc]

private theorem lam_two {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E)
    (S : Type) [CommRing S] [Algebra A S] (s t : S) :
    D.D S (s ⊗ₜ 1 + t ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), algebraMap A S (D.lam i x) * s ^ (n - i) * t ^ i := by
  obtain ⟨h1, h2⟩ := d_poly D ![1, x]
  obtain ⟨c, hc⟩ := hom_two _ h1
  have key : ∀ (S : Type) [CommRing S] [Algebra A S] (s t : S),
      D.D S (s ⊗ₜ 1 + t ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), algebraMap A S (c i) * s ^ (n - i) * t ^ i := by
    intro S _ _ s t
    rw [← hc, ← h2]
    simp [Fin.sum_univ_two]
  have hl : ∀ j ∈ Finset.range (n + 1), D.lam j x = c j := by
    intro j hj
    have hj' : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
    have hchi : D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * c i) * X ^ (n - i) := by
      rw [Det.chi, sub_eq_add_neg, ← neg_tmul, key]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow, map_neg,
        map_one]
      ring
    rw [Det.lam, hchi, finset_sum_coeff, Finset.sum_eq_single j]
    · rw [coeff_C_mul_X_pow, if_pos rfl, ← mul_assoc, ← mul_pow]; simp
    · intro i hi hij
      have : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · intro h; exact absurd hj h
  rw [key]
  exact Finset.sum_congr rfl fun i hi => by rw [hl i hi]

theorem UpperTheory.V.CA.d_chi :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E), D.lam 0 x = 1 ∧ D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i x) * X ^ (n - i) ∧ D.D A[X] (1 + X ⊗ₜ x) = ∑ i ∈ Finset.range (n + 1), C (D.lam i x) * X ^ i ∧ D.lam n x = D.val x ∧ (D.chi x).Monic ∧ (D.chi x).natDegree ≤ n ∧ ∀ (a : A) (i : ℕ), i ≤ n → D.lam i (a • x) = a ^ i * D.lam i x := by
  intro n A E _ _ _ D x
  have h0 : D.lam 0 x = 1 := by
    have h := lam_two D x A 1 0
    rw [zero_tmul, add_zero, ← Algebra.TensorProduct.one_def, map_one, Finset.sum_range_succ'] at h
    simpa using h.symm
  have hchi : D.chi x = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i x) * X ^ (n - i) := by
    conv_lhs => rw [Det.chi, sub_eq_add_neg, ← neg_tmul, lam_two]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow, map_neg,
      map_one]
    ring
  have h1 : ∀ y : E, D.D A[X] (1 + X ⊗ₜ y) = ∑ i ∈ Finset.range (n + 1), C (D.lam i y) * X ^ i := by
    intro y
    rw [Algebra.TensorProduct.one_def, lam_two]
    simp
  have hdeg : (D.chi x).natDegree ≤ n := by
    rw [hchi]
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)
  refine ⟨h0, hchi, h1 x, ?_, ?_, hdeg, ?_⟩
  · have h := lam_two D x A 0 1
    rw [zero_tmul, zero_add, Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => by
      have : n - i ≠ 0 := by rw [Finset.mem_range] at hi; omega
      simp [this])] at h
    change _ = D.D A (1 ⊗ₜ x)
    rw [h]; simp
  · refine monic_of_natDegree_le_of_coeff_eq_one n hdeg ?_
    simpa [Det.lam] using h0
  · intro a j hj
    have h := h1 (a • x)
    rw [← smul_tmul, Algebra.TensorProduct.one_def, lam_two] at h
    have h' : ∑ i ∈ Finset.range (n + 1), C (a ^ i * D.lam i x) * X ^ i =
        ∑ i ∈ Finset.range (n + 1), C (D.lam i (a • x)) * X ^ i := by
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_pow,
        smul_eq_C_mul]
      ring
    have h2 := congrArg (fun p => p.coeff j) h'
    simp only [finset_sum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff, hj,
      if_true] at h2
    exact h2.symm
