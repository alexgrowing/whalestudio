import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsHermFormCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

namespace HermitianFormComparison

theorem sum_norm_sq_unitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * star U = 1)
    (x : Fin n → ℂ) : ∑ k, ‖(star U *ᵥ x) k‖ ^ 2 = (star x ⬝ᵥ x).re := by
  have h1 : star (star U *ᵥ x) ⬝ᵥ (star U *ᵥ x) = star x ⬝ᵥ x := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, star_eq_conjTranspose,
      conjTranspose_conjTranspose, ← star_eq_conjTranspose, hU, vecMul_one]
  rw [← h1]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem re_quad_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re = ∑ k, hA.eigenvalues k *
      ‖(star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) k‖ ^ 2 := by
  set U : Matrix (Fin n) (Fin n) ℂ := (↑hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hspec : A = U * diagonal (fun k => (hA.eigenvalues k : ℂ)) * star U := by
    have h := hA.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h
    exact h
  set y : Fin n → ℂ := star U *ᵥ x with hy
  have hq : star x ⬝ᵥ (A *ᵥ x) = star y ⬝ᵥ (diagonal (fun k => (hA.eigenvalues k : ℂ)) *ᵥ y) := by
    conv_lhs => rw [hspec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hy, star_mulVec,
      star_eq_conjTranspose U, conjTranspose_conjTranspose]
  rw [hq]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]

theorem eigenvectorUnitary_mul_star {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2

theorem re_quad_le {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (M *ᵥ x)).re ≤ (1 + ∑ k, hM.1.eigenvalues k) * (star x ⬝ᵥ x).re := by
  rw [re_quad_eq hM.1, ← sum_norm_sq_unitary _ (eigenvectorUnitary_mul_star hM.1), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hle : hM.1.eigenvalues k ≤ ∑ j, hM.1.eigenvalues j :=
    Finset.single_le_sum (f := hM.1.eigenvalues) (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ k)
  linarith

theorem re_quad_ge {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.PosDef) (x : Fin n → ℂ) :
    (1 + ∑ k, (hN.1.eigenvalues k)⁻¹)⁻¹ * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (N *ᵥ x)).re := by
  rw [re_quad_eq hN.1, ← sum_norm_sq_unitary _ (eigenvectorUnitary_mul_star hN.1), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hpos := hN.eigenvalues_pos k
  have hle : (hN.1.eigenvalues k)⁻¹ ≤ ∑ j, (hN.1.eigenvalues j)⁻¹ :=
    Finset.single_le_sum (f := fun j => (hN.1.eigenvalues j)⁻¹)
      (fun j _ => (inv_pos.mpr (hN.eigenvalues_pos j)).le) (Finset.mem_univ k)
  rw [inv_le_comm₀ (by linarith [inv_pos.mpr hpos]) hpos]
  linarith

end HermitianFormComparison

open HermitianFormComparison in

theorem HermFormCompare.proof : HermFormCompare.Statement := by
  intro n M N hM hN
  set L : ℝ := 1 + ∑ k, hM.1.eigenvalues k with hL
  set m : ℝ := (1 + ∑ k, (hN.1.eigenvalues k)⁻¹)⁻¹ with hm
  have hL0 : 0 < L := by
    have : 0 ≤ ∑ k, hM.1.eigenvalues k := Finset.sum_nonneg fun k _ => (hM.eigenvalues_pos k).le
    linarith
  have hm0 : 0 < m := by
    have : 0 ≤ ∑ k, (hN.1.eigenvalues k)⁻¹ :=
      Finset.sum_nonneg fun k _ => (inv_pos.mpr (hN.eigenvalues_pos k)).le
    exact inv_pos.mpr (by linarith)
  refine ⟨L / m, div_pos hL0 hm0, fun x => ?_⟩
  have hup := re_quad_le hM.posSemidef x
  have hlo := re_quad_ge hN x
  calc (star x ⬝ᵥ (M *ᵥ x)).re ≤ L * (star x ⬝ᵥ x).re := hup
    _ = L / m * (m * (star x ⬝ᵥ x).re) := by field_simp
    _ ≤ L / m * (star x ⬝ᵥ (N *ᵥ x)).re :=
        mul_le_mul_of_nonneg_left hlo (div_pos hL0 hm0).le

end GroundTheory.Heights₂.Heights
