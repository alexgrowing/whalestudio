import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace GlobalTheory.PeriodFrame

open GlobalTheory.ShFam.Hor

def combMat {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun k i => ∑ m, (ε i m : ℂ) * l m k

def perTau {n g r₀ r : ℕ} (a : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ)
    (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ) (s : Fin n → ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (D : ℂ) • ((combMat (ζ (logExp a s)) α)⁻¹ * combMat (lam s) φ)

theorem combMat_comb {g r r' : ℕ} (w : Fin r' → Fin g → ℂ) (l : Fin r → Fin g → ℂ) (c : Matrix (Fin r') (Fin r) ℤ)
    (α : Matrix (Fin g) (Fin r') ℚ) (hw : ∀ i, w i = ∑ j, c i j • l j) :
    combMat w α = combMat l (α * c.map (Int.cast : ℤ → ℚ)) := by
  ext k i
  simp only [combMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, hw, Finset.sum_apply, Pi.smul_apply,
    zsmul_eq_mul]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by
    simp only [Pi.mul_apply, Pi.intCast_apply]; ring

theorem combMat_add_mul {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) :
    combMat l (φ + bᵀ * ε) = combMat l φ + combMat l ε * b.map (Rat.cast : ℚ → ℂ) := by
  ext k j
  simp only [combMat, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem combMat_shift {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) (D : ℕ) (Bk : Matrix (Fin g) (Fin g) ℤ) (hP : IsUnit (combMat l ε).det)
    (hB : ∀ i j, (Bk i j : ℚ) = D * b i j) :
    (D : ℂ) • ((combMat l ε)⁻¹ * combMat l (φ + bᵀ * ε)) =
      (D : ℂ) • ((combMat l ε)⁻¹ * combMat l φ) + Bk.map (Int.cast : ℤ → ℂ) := by
  rw [combMat_add_mul, Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, smul_add]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  have h := congrArg (Rat.cast : ℚ → ℂ) (hB i j)
  push_cast at h
  rw [h]

theorem shift_mem {n a : ℕ} (ha : a ≤ n) (k : Fin a) {s : Fin n → ℂ} (hs : s ∈ logDom n a) :
    s + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I) ∈ logDom n a ∧
      logExp a (s + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) = logExp a s := by
  simp only [logDom, Set.mem_setOf_eq] at hs ⊢
  constructor
  · intro j
    have h := hs j
    by_cases hj : j = Fin.castLE ha k
    · subst hj
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp [Fin.coe_castLE, k.isLt]
      simp only [hk, if_true] at h ⊢
      simpa [Pi.add_apply] using h
    · simpa [Pi.add_apply, Pi.single_eq_of_ne hj] using h
  · funext j
    by_cases hj : j = Fin.castLE ha k
    · subst hj
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp [Fin.coe_castLE, k.isLt]
      simp only [logExp, hk, if_true, Pi.add_apply, Pi.single_eq_same]
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, _root_.mul_one]
    · simp [logExp, Pi.single_eq_of_ne hj]

end GlobalTheory.PeriodFrame
