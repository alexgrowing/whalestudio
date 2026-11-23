import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DComm

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem UpperTheory.V.CA.d_tr_coeff {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    (x : E) (i : ℕ) (hi : i ≤ n) : (D.D A[X] (1 + X ⊗ₜ x)).coeff i = D.lam i x := by
  rw [(d_chi D x).2.2.1, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff, hi]

private theorem UpperTheory.V.CA.d_tr_dual {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    (hn : 1 ≤ n) (x : E) :
    D.D (DualNumber A) (1 + DualNumber.eps ⊗ₜ x) = 1 + D.tr x • DualNumber.eps := by
  have h := D.nat A[X] (DualNumber A) (aeval DualNumber.eps) (1 + X ⊗ₜ x)
  rw [map_add, map_one, Algebra.TensorProduct.map_tmul, aeval_X, AlgHom.id_apply] at h
  rw [h, (d_chi D x).2.2.1]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', (d_chi D x).1]
  have h2 : ∀ k : ℕ, (DualNumber.eps : DualNumber A) ^ (k + 1 + 1) = 0 := fun k => by
    rw [pow_succ, pow_succ, mul_assoc, DualNumber.eps_mul_eps, mul_zero]
  simp only [map_add, map_sum, map_mul, map_pow, aeval_X, aeval_C, h2, mul_zero, Finset.sum_const_zero]
  simp [Det.tr, Algebra.smul_def, add_comm]

theorem UpperTheory.V.CA.d_tr :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), (1 ≤ n → ∃ t : E →ₗ[A] A, ∀ x, t x = D.tr x) ∧ (∀ i x y, D.lam i (x * y) = D.lam i (y * x)) ∧ (1 ≤ n → D.tr 1 = n) := by
  intro n A E _ _ _ D
  refine ⟨fun hn => ⟨⟨⟨D.tr, fun x y => ?_⟩, fun a x => ?_⟩, fun _ => rfl⟩, fun i x y => ?_, fun hn => ?_⟩
  · have h : (1 + DualNumber.eps ⊗ₜ (x + y) : DualNumber A ⊗[A] E) =
        (1 + DualNumber.eps ⊗ₜ x) * (1 + DualNumber.eps ⊗ₜ y) := by
      rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, DualNumber.eps_mul_eps, zero_tmul,
        tmul_add]
      simp only [one_mul, mul_one, add_zero]
      abel
    have h2 := congrArg (D.D (DualNumber A)) h
    rw [map_mul, d_tr_dual D hn, d_tr_dual D hn, d_tr_dual D hn] at h2
    have h3 := congrArg TrivSqZeroExt.snd h2
    simpa [add_comm] using h3
  · simpa [Det.tr] using (d_chi D x).2.2.2.2.2.2 a 1 hn
  · have h : ∀ j ≤ n, D.lam j (x * y) = D.lam j (y * x) := fun j hj => by
      have := d_comm D A[X] (X ⊗ₜ x) (1 ⊗ₜ y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
      rw [← d_tr_coeff D _ j hj, ← d_tr_coeff D _ j hj, this]
    have h2 : D.chi (x * y) = D.chi (y * x) := by
      rw [(d_chi D (x * y)).2.1, (d_chi D (y * x)).2.1]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
    rw [Det.lam, Det.lam, h2]
  · rw [Det.tr, ← d_tr_coeff D 1 1 hn]
    have h : (1 + X ⊗ₜ 1 : A[X] ⊗[A] E) = (1 + X : A[X]) • 1 := by
      rw [Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one, add_tmul]
    rw [h, D.homog, map_one, mul_one, coeff_one_add_X_pow]
    simp
