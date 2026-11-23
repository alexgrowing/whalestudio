import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

private lemma expand_sandwich {ι : Type*} [Fintype ι] [DecidableEq ι] (M X X' Y : Matrix ι ι ℂ) (c a b d : ℂ)
    (h1 : X' * M = a • Y) (h2 : M * X = b • Y) (h3 : X' * M * X = d • Y) :
    (1 - c • X') * M * (1 - c • X) = M + (c * c * d - c * a - c * b) • Y := by
  have e : (1 - c • X') * M * (1 - c • X) =
      M - c • (X' * M) - c • (M * X) + (c * c) • (X' * M * X) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub,
      smul_smul]
    abel
  rw [e, h3, h1, h2]
  simp only [smul_smul, sub_smul]
  abel

theorem EigenReflection.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    EigenReflection.Statement ι := by
  intro H P hmaj ε hε v hv hAv
  obtain ⟨hP, hH, -, hPHP⟩ := hmaj
  have hPh : Pᴴ = P := hP.isHermitian
  have hHh : Hᴴ = H := hH
  set y : ι → ℂ := P *ᵥ v with hy
  set q : ℂ := star v ⬝ᵥ (P *ᵥ v) with hqdef
  have hqpos : 0 < q := hP.dotProduct_mulVec_pos hv
  have hq0 : q ≠ 0 := hqpos.ne'
  have hqstar : star q = q := Complex.conj_eq_iff_im.mpr (Complex.pos_iff.mp hqpos).2.symm
  have hεstar : star ε = ε := by rcases hε with rfl | rfl <;> simp
  set c : ℂ := 2 / q with hc
  have hcstar : star c = c := by rw [hc, star_div₀, hqstar]; simp
  have hcq : c * q = 2 := by rw [hc]; field_simp

  have hwy : star v ᵥ* P = star y := by rw [hy, star_mulVec, hPh]
  have hyv : star y ⬝ᵥ v = q := by rw [← hwy, ← dotProduct_mulVec]

  have hHv : H *ᵥ v = ε • y := by
    have : H *ᵥ v = P *ᵥ ((H⁻¹ * P) *ᵥ v) := by rw [mulVec_mulVec, ← Matrix.mul_assoc, hPHP]
    rw [this, show (H⁻¹ * P) *ᵥ v = ε • v from hAv, mulVec_smul]
  have hvH : star v ᵥ* H = ε • star y := by
    rw [← hHh, ← star_mulVec, hHv, star_smul, hεstar]

  have hR : pReflection P v = 1 - c • vecMulVec v (star y) := by
    rw [pReflection, ← hqdef, ← hc, vecMulVec_mul, hwy]
  have hRh : (pReflection P v)ᴴ = 1 - c • vecMulVec y (star v) := by
    rw [hR, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hcstar,
      conjTranspose_vecMulVec, star_star]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hRh, hR]
    have h1 : vecMulVec y (star v) * P = (1 : ℂ) • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hwy, one_smul]
    have h2 : P * vecMulVec v (star y) = (1 : ℂ) • vecMulVec y (star y) := by
      rw [mul_vecMulVec, ← hy, one_smul]
    have h3 : vecMulVec y (star v) * P * vecMulVec v (star y) = q • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hwy, vecMulVec_mul_vecMulVec, hyv, vecMulVec_smul]
    rw [expand_sandwich P _ _ _ c 1 1 q h1 h2 h3]
    have : c * c * q - c * 1 - c * 1 = 0 := by
      rw [mul_assoc, hcq]; ring
    rw [this, zero_smul, add_zero]
  · rw [hRh, hR]
    have h1 : vecMulVec y (star v) * H = ε • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hvH, vecMulVec_smul]
    have h2 : H * vecMulVec v (star y) = ε • vecMulVec y (star y) := by
      rw [mul_vecMulVec, hHv]
      ext i j
      simp [vecMulVec_apply, mul_assoc]
    have h3 : vecMulVec y (star v) * H * vecMulVec v (star y) = (ε * q) • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hvH, vecMulVec_mul_vecMulVec, smul_dotProduct, hyv, vecMulVec_smul]
      rfl
    rw [expand_sandwich H _ _ _ c ε ε (ε * q) h1 h2 h3]
    have : c * c * (ε * q) - c * ε - c * ε = 0 := by
      have : c * c * (ε * q) = (c * q) * c * ε := by ring
      rw [this, hcq]; ring
    rw [this, zero_smul, add_zero]
  · rw [hR, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hyv]
    rw [op_smul_eq_smul, smul_smul, hcq, two_smul]; abel
  · intro u hu
    have hyu : star y ⬝ᵥ u = 0 := by rw [← hwy, ← dotProduct_mulVec, hu]
    rw [hR, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hyu]
    simp

end GroundTheory.Heights₂.Heights.FiniteCovolume
