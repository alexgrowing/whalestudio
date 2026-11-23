import Mathlib
open Matrix Polynomial

namespace GlobalTheory

theorem csr_transpose_aeval {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    (aeval A p)ᵀ = aeval Aᵀ p := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [transpose_smul, transpose_pow]

theorem csr_map_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    (aeval A p).map σ = aeval (A.map σ) (p.map σ) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range' (n := p.natDegree + 1)]
  · rw [← RingHom.mapMatrix_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpow : (A ^ i).map σ = (A.map σ) ^ i := by
      rw [← RingHom.mapMatrix_apply, map_pow]; rfl
    rw [coeff_map, RingHom.mapMatrix_apply, ← hpow]
    ext a b
    simp [Matrix.smul_apply]
  · exact Nat.lt_succ_of_le (natDegree_map_le)

theorem csr_pow_mul_pow {K : Type} [Field K] {n : ℕ} (γ B : Matrix (Fin n) (Fin n) K)
    (h : γ * B = 1) (d i : ℕ) (hi : i ≤ d) : γ ^ d * B ^ i = γ ^ (d - i) := by
  have key : ∀ j, γ ^ j * B ^ j = 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc γ, h, one_mul, ih]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [add_comm i e, pow_add, mul_assoc, key, mul_one, Nat.add_sub_cancel]

theorem csr_reverse {K : Type} [Field K] {n : ℕ} (γ B : Matrix (Fin n) (Fin n) K)
    (h : γ * B = 1) (P : K[X]) :
    γ ^ P.natDegree * aeval B P = aeval γ P.reverse := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range' (n := P.natDegree + 1), Finset.mul_sum]
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : P.natDegree + 1 - 1 - i = P.natDegree - i := by omega
    rw [e1, mul_smul_comm, csr_pow_mul_pow γ B h _ _ (Nat.sub_le _ _), coeff_reverse,
      revAt_le hi']
    have e2 : P.natDegree - (P.natDegree - i) = i := by omega
    rw [e2]
  · exact Nat.lt_succ_of_le (reverse_natDegree_le P)

end GlobalTheory

namespace GlobalTheory

theorem csr_ker_orth_range {K : Type} [Field K] (σ : K →+* K) {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hγ : (γ.map σ)ᵀ * γ = 1) (Q : K[X])
    (hQ : C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse) (x z : Fin n → K)
    (hx : aeval γ Q *ᵥ x = 0) : ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 := by
  have hγB : γ * (γ.map σ)ᵀ = 1 := mul_eq_one_comm.mp hγ
  have hMt : ((aeval γ Q).map σ)ᵀ = aeval (γ.map σ)ᵀ (Q.map σ) := by
    rw [csr_map_aeval, csr_transpose_aeval]
  have hrev : aeval γ (Q.map σ).reverse = σ (Q.coeff 0) • aeval γ Q := by
    rw [← hQ, aeval_mul, aeval_C, Algebra.smul_def]
  have hBd : (γ.map σ)ᵀ ^ (Q.map σ).natDegree * γ ^ (Q.map σ).natDegree = 1 := by
    rw [csr_pow_mul_pow _ _ hγ _ _ le_rfl, Nat.sub_self, pow_zero]
  have hBP : aeval (γ.map σ)ᵀ (Q.map σ)
      = (γ.map σ)ᵀ ^ (Q.map σ).natDegree * (σ (Q.coeff 0) • aeval γ Q) := by
    rw [← hrev, ← csr_reverse γ _ hγB, ← mul_assoc, hBd, one_mul]
  have hBx : aeval (γ.map σ)ᵀ (Q.map σ) *ᵥ x = 0 := by
    rw [hBP, ← mulVec_mulVec, smul_mulVec, hx, smul_zero, mulVec_zero]
  have expand : ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k
      = ∑ l, σ (z l) * ((((aeval γ Q).map σ)ᵀ) *ᵥ x) l := by
    simp only [mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
      transpose_apply, map_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [expand, hMt, hBx]
  simp

end GlobalTheory
