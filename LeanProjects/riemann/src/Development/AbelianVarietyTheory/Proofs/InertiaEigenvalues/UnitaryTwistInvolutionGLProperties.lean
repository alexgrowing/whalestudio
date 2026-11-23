import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwConj
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.Tw Matrix

namespace GlobalTheory.Tw.PhiConjugateTranspose

variable {n : ℕ} {R : Type} [CommRing R]

theorem phi_apply (i k : Fin n) : Phi n R i k = if k = i.rev then (-1 : R) ^ (i : ℕ) else 0 := by
  simp only [Phi, of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  omega

theorem phi_conj_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Phi n R * A * (Phi n R)ᵀ) i j = (-1 : R) ^ (i : ℕ) * A i.rev j.rev * (-1 : R) ^ (j : ℕ) := by
  simp [mul_apply, phi_apply, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem phi_mul_transpose : Phi n R * (Phi n R)ᵀ = 1 := by
  have := phi_conj_apply (n := n) (R := R) 1
  ext i j
  have h := this i j
  rw [Matrix.mul_one] at h
  rw [h, one_apply, one_apply]
  by_cases hij : i = j
  · subst hij; simp [← mul_pow]
  · simp [hij]

theorem phi_transpose_mul : (Phi n R)ᵀ * Phi n R = 1 := mul_eq_one_comm.mp phi_mul_transpose

theorem phi_mul_phi : Phi n R * Phi n R = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i k
  simp only [mul_apply, phi_apply, Matrix.smul_apply, one_apply, smul_eq_mul, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  by_cases h : k = i
  · subst h
    simp only [if_true, mul_one]
    rw [← pow_add, Fin.val_rev]
    have hk := k.isLt
    rw [show (k : ℕ) + (n - ((k : ℕ) + 1)) = n - 1 by omega]
  · simp [h, Ne.symm h]

theorem phi_inv : (Phi n R)⁻¹ = (Phi n R)ᵀ := Matrix.inv_eq_left_inv phi_transpose_mul

theorem phi_transpose_inv : ((Phi n R)ᵀ)⁻¹ = Phi n R := Matrix.inv_eq_left_inv phi_mul_transpose

theorem conj_inv (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)⁻¹ = Phi n R * A⁻¹ * (Phi n R)ᵀ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, phi_inv, phi_transpose_inv, Matrix.mul_assoc]

theorem det_conj (A : Matrix (Fin n) (Fin n) R) : (Phi n R * A * (Phi n R)ᵀ).det = A.det := by
  rw [det_mul, det_mul, mul_comm (Phi n R).det, mul_assoc, ← det_mul, phi_mul_transpose, det_one, mul_one]

variable [StarRing R]

theorem phi_conjTranspose : (Phi n R)ᴴ = (Phi n R)ᵀ := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply, Phi, of_apply]
  split_ifs <;> simp

theorem phi_transpose_conjTranspose : ((Phi n R)ᵀ)ᴴ = Phi n R := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply, Phi, of_apply]
  split_ifs <;> simp

theorem conj_conjTranspose (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)ᴴ = Phi n R * Aᴴ * (Phi n R)ᵀ := by
  rw [conjTranspose_mul, conjTranspose_mul, phi_conjTranspose, phi_transpose_conjTranspose, Matrix.mul_assoc]

theorem theta_eq (g : Matrix (Fin n) (Fin n) R) : theta g = Phi n R * (g⁻¹)ᴴ * (Phi n R)ᵀ := rfl

theorem theta_mul (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by
  simp only [theta_eq, Matrix.mul_inv_rev, conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), phi_transpose_mul, Matrix.one_mul]

theorem theta_one : theta (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [theta_eq, inv_one, conjTranspose_one, Matrix.mul_one, phi_mul_transpose]

theorem det_theta (g : Matrix (Fin n) (Fin n) R) : (theta g).det = star (g⁻¹).det := by
  rw [theta_eq, det_conj, det_conjTranspose]

theorem theta_isUnit {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : IsUnit (theta g) := by
  rw [isUnit_iff_isUnit_det, det_theta]
  exact (isUnit_nonsing_inv_det _ ((isUnit_iff_isUnit_det g).mp hg)).star

theorem theta_theta {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by
  have hd := (isUnit_iff_isUnit_det g).mp hg
  rw [theta_eq (theta g), theta_eq g, conj_inv, conj_conjTranspose, ← conjTranspose_nonsing_inv,
    nonsing_inv_nonsing_inv _ hd, conjTranspose_conjTranspose]
  have h2 : (Phi n R)ᵀ * (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← transpose_mul, phi_mul_phi, transpose_smul, transpose_one]
  calc Phi n R * (Phi n R * g * (Phi n R)ᵀ) * (Phi n R)ᵀ
      = (Phi n R * Phi n R) * g * ((Phi n R)ᵀ * (Phi n R)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = g := by
      rw [phi_mul_phi, h2, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, ← mul_pow]
      simp

theorem theta_blockTriangular {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) (ht : g.BlockTriangular id) :
    (theta g).BlockTriangular id := by
  have : Invertible g := hg.invertible
  have hi : (g⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular ht
  intro i j hji
  rw [theta_eq, phi_conj_apply, conjTranspose_apply, hi]
  · simp
  · simpa [Fin.rev_lt_rev] using hji

end GlobalTheory.Tw.PhiConjugateTranspose

open GlobalTheory.Tw.PhiConjugateTranspose in
theorem GlobalTheory.Tw.theta_props : ∀ (n : ℕ) (R : Type) [CommRing R] [StarRing R], (Phi n R * (Phi n R)ᵀ = 1) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit (theta g) ∧ theta (theta g) = g) ∧ (∀ g h : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit h → theta (g * h) = theta g * theta h) ∧ (∀ x δ : Matrix (Fin n) (Fin n) R, IsUnit x → IsUnit δ → nrm (twConj x δ) = x⁻¹ * nrm δ * x) ∧ (∀ u δ : Matrix (Fin n) (Fin n) R, IsUnit u → IsUnit δ → nrm (δ * theta u) = nrm δ * ((theta δ)⁻¹ * theta u * theta δ) * u) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → g.BlockTriangular id → (theta g).BlockTriangular id) ∧ ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → (theta g).det * star g.det = 1 := by
  intro n R _ _
  refine ⟨phi_mul_transpose, fun g hg => ⟨theta_isUnit hg, theta_theta hg⟩, fun g h _ _ => theta_mul g h, ?_, ?_,
    fun g hg ht => theta_blockTriangular hg ht, ?_⟩
  · intro x δ hx _
    have hxd := (isUnit_iff_isUnit_det x).mp hx
    simp only [nrm, twConj, theta_mul, theta_theta hx]
    have h1 : theta x * theta x⁻¹ = 1 := by rw [← theta_mul, mul_nonsing_inv _ hxd, theta_one]
    calc x⁻¹ * δ * theta x * (theta x⁻¹ * theta δ * x)
        = x⁻¹ * δ * (theta x * theta x⁻¹) * theta δ * x := by simp only [Matrix.mul_assoc]
      _ = x⁻¹ * (δ * theta δ) * x := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  · intro u δ hu hδ
    have htd := (isUnit_iff_isUnit_det _).mp (theta_isUnit hδ)
    simp only [nrm, theta_mul, theta_theta hu]
    calc δ * theta u * (theta δ * u)
        = δ * (theta δ * (theta δ)⁻¹) * theta u * theta δ * u := by
          rw [mul_nonsing_inv _ htd, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = δ * theta δ * ((theta δ)⁻¹ * theta u * theta δ) * u := by simp only [Matrix.mul_assoc]
  · intro g hg
    have hd := (isUnit_iff_isUnit_det g).mp hg
    rw [det_theta, ← star_mul, ← det_mul, mul_nonsing_inv _ hd, det_one, star_one]
