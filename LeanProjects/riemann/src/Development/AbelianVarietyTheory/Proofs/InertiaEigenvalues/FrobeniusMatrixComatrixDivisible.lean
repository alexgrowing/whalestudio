import Mathlib
open Matrix

namespace GlobalTheory

theorem frobenius_matrix_comatrix_divisible {R : Type} [CommRing R] [IsDomain R] (d N N₀ q : ℕ) (p : Fin d → ℕ) (ξ : R)
    (A A' B B' c c' V₀ V₀' : Matrix (Fin d) (Fin d) R) (hξ : ξ ≠ 0) (hB : B * B' = 1) (hc : c * c' = 1)
    (hV : V₀ * V₀' = 1) (hA : A * A' = ξ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hid : ξ ^ q • (A * B * c) = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j)))
    (hN : N₀ ≤ N) (hp : ∀ i, |(p i : ℤ) - q| ≤ N₀) :
    (∀ i j, ξ ^ (N - N₀) ∣ A i j) ∧ ∀ i j, ξ ^ (N - N₀) ∣ A' i j := by
  have hp1 : ∀ k, q ≤ p k + N₀ := fun k => by
    have := (abs_le.mp (hp k)).1; omega
  have hp2 : ∀ k, p k ≤ q + N₀ := fun k => by
    have := (abs_le.mp (hp k)).2; omega
  have hq0 : ξ ^ q ≠ 0 := pow_ne_zero _ hξ
  have cancel : ∀ (s : R), s ≠ 0 → ∀ M M' : Matrix (Fin d) (Fin d) R, s • M = s • M' → M = M' := by
    intro s hs M M' h
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hs this
  have hA1 : ξ ^ q • A = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j) * (c' * B')) := by
    have : A = A * B * c * (c' * B') := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (A * B) c c', hc, Matrix.mul_one, Matrix.mul_assoc, hB,
        Matrix.mul_one]
    conv_lhs => rw [this]
    rw [← Matrix.smul_mul, hid, Matrix.smul_mul]
  constructor
  · intro i j
    have e := congrFun (congrFun hA1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    rw [Matrix.mul_apply] at e
    simp only [Matrix.mul_diagonal] at e
    have hdiv : ξ ^ q * ξ ^ (N - N₀) ∣ ξ ^ q * A i j := by
      rw [e, Finset.mul_sum]
      apply Finset.dvd_sum
      intro k _
      have h1 : ξ ^ q * ξ ^ (N - N₀) ∣ ξ ^ N * ξ ^ p k := by
        rw [← pow_add, ← pow_add]; exact pow_dvd_pow _ (by have := hp1 k; omega)
      exact h1.trans ⟨V₀ i k * (c' * B') k j, by ring⟩
    exact (mul_dvd_mul_iff_left hq0).mp hdiv
  · set D' : Matrix (Fin d) (Fin d) R := Matrix.diagonal (fun k => ξ ^ (N₀ + q - p k)) with hD'
    have hDD : Matrix.diagonal (fun j => ξ ^ p j) * D' = ξ ^ (N₀ + q) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [hD', Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        rw [← pow_add]; congr 1; have := hp2 i; omega
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    set Z := B * c * D' * V₀' with hZ
    have hAZ : ξ ^ q • (A * Z) = ξ ^ (N + (N₀ + q)) • (1 : Matrix (Fin d) (Fin d) R) := by
      have : A * Z = A * B * c * D' * V₀' := by simp only [hZ, Matrix.mul_assoc]
      rw [this, Matrix.mul_assoc (A * B * c), ← Matrix.smul_mul, hid, Matrix.smul_mul,
        Matrix.mul_assoc V₀, ← Matrix.mul_assoc _ D', hDD, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, hV, smul_smul, ← pow_add]
    have hAZ2 : A * (ξ ^ (N - N₀) • Z) = A * A' := by
      apply cancel _ hq0
      rw [Matrix.mul_smul, smul_comm, hAZ, smul_smul, hA, smul_smul, ← pow_add, ← pow_add]
      congr 2; omega
    have hdetA : A.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hA
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
      exact pow_ne_zero _ (pow_ne_zero _ hξ) this.symm
    have hA' : A' = ξ ^ (N - N₀) • Z := by
      apply cancel _ hdetA
      rw [← Matrix.one_mul A', ← Matrix.one_mul (ξ ^ (N - N₀) • Z), ← Matrix.smul_mul, ← Matrix.smul_mul,
        ← Matrix.adjugate_mul, Matrix.mul_assoc, Matrix.mul_assoc, hAZ2]
    intro i j
    rw [hA', Matrix.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _

end GlobalTheory
