import Mathlib
open Matrix

theorem GlobalTheory.ht_operator_of_galois_relations : ∀ {k : Type} [Field k] (d N q : ℕ) (p : Fin d → ℕ) (a b z w : k) (y y' v v₀ e r sy sv : Matrix (Fin d) (Fin d) k), a ≠ 0 → b ≠ 0 → z * w = 1 → y * y' = a ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) k) → y * v₀ = a ^ N • v → a ^ N • (r * sy) = b ^ N • (y * e) → r * sv * Matrix.diagonal (fun j => w ^ p j) = w ^ q • v → sy * v₀ = b ^ N • sv → ∃ u : Matrix (Fin d) (Fin d) k, u * y = y * e ∧ u * v = v * Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
  intro k _ d N q p a b z w y y' v v₀ e r sy sv ha hb hzw hy hyv hr hsv hsy
  have hz : z ≠ 0 := left_ne_zero_of_mul_eq_one hzw
  have hw : w = z⁻¹ := eq_inv_of_mul_eq_one_right hzw
  have haN : a ^ N ≠ 0 := pow_ne_zero _ ha
  have hbN : b ^ N ≠ 0 := pow_ne_zero _ hb
  have ha2 : a ^ (2 * N) ≠ 0 := pow_ne_zero _ ha
  have hy' : y' * y = a ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) k) := by
    have h1 : y * ((a ^ (2 * N))⁻¹ • y') = 1 := by
      rw [Matrix.mul_smul, hy, smul_smul, inv_mul_cancel₀ ha2, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.smul_mul] at h2
    calc y' * y = a ^ (2*N) • ((a ^ (2 * N))⁻¹ • (y' * y)) := by
          rw [smul_smul, mul_inv_cancel₀ ha2, one_smul]
      _ = _ := by rw [h2]
  have hD : r * sv = v * Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
    have hdd : Matrix.diagonal (fun j => w ^ p j) * Matrix.diagonal (fun j => z ^ p j) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext j; rw [← mul_pow, mul_comm, hzw, one_pow]
    have hdiag : w ^ q • Matrix.diagonal (fun j => z ^ p j)
        = Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
        rw [zpow_sub₀ hz, zpow_natCast, zpow_natCast, hw, inv_pow, div_eq_mul_inv, mul_comm]
      · simp [Matrix.diagonal_apply_ne _ hij]
    calc r * sv = r * sv * (Matrix.diagonal (fun j => w ^ p j) * Matrix.diagonal (fun j => z ^ p j)) := by
          rw [hdd, Matrix.mul_one]
      _ = (w ^ q • v) * Matrix.diagonal (fun j => z ^ p j) := by rw [← Matrix.mul_assoc, hsv]
      _ = _ := by rw [Matrix.smul_mul, ← Matrix.mul_smul, hdiag]
  have hyev : y * e * v₀ = a ^ N • (r * sv) := by
    have h1 : b ^ N • (y * e * v₀) = b ^ N • (a ^ N • (r * sv)) := by
      rw [← Matrix.smul_mul, ← hr, Matrix.smul_mul, Matrix.mul_assoc, hsy, Matrix.mul_smul, smul_comm]
    exact smul_right_injective _ hbN h1
  have hy'v : y' * v = a ^ N • v₀ := by
    have h1 : a ^ N • (y' * v) = a ^ N • (a ^ N • v₀) := by
      rw [← Matrix.mul_smul, ← hyv, ← Matrix.mul_assoc, hy', Matrix.smul_mul, Matrix.one_mul, smul_smul,
        ← pow_add, two_mul]
    exact smul_right_injective _ haN h1
  refine ⟨(a ^ (2 * N))⁻¹ • (y * e * y'), ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_assoc, hy', Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ ha2, one_smul]
  · have hc : (a ^ (2 * N))⁻¹ * a ^ N * a ^ N = 1 := by
      rw [mul_assoc, ← pow_add, ← two_mul, inv_mul_cancel₀ ha2]
    rw [Matrix.smul_mul, Matrix.mul_assoc, hy'v, Matrix.mul_smul, hyev, smul_smul, smul_smul, hc, one_smul, hD]
