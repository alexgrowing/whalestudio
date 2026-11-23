import Mathlib

namespace ReciprocityTheory.L2DbarEstimates.Y

open Matrix
open scoped MatrixOrder

theorem uniLat_det_one_add {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) : (1 + Q).det = ∏ i, (1 + hQ.1.eigenvalues i) := by
  have hs := hQ.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U := hQ.1.eigenvectorUnitary with hU
  have hUU : (U : Matrix ι ι ℝ) * star (U : Matrix ι ι ℝ) = 1 := Unitary.coe_mul_star_self U
  have hUU' : star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ) = 1 := Unitary.coe_star_mul_self U
  have e : 1 + Q = (U : Matrix ι ι ℝ) * (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues))
      * star (U : Matrix ι ι ℝ) := by
    conv_lhs => rw [hs]
    rw [mul_add, add_mul, mul_one, hUU]
  have hd : ((U : Matrix ι ι ℝ)).det * (star (U : Matrix ι ι ℝ)).det = 1 := by
    rw [← det_mul, hUU, det_one]
  rw [e, det_mul, det_mul, mul_comm ((U : Matrix ι ι ℝ).det), mul_assoc, hd, mul_one,
    ← diagonal_one, diagonal_add, det_diagonal]
  simp [RCLike.ofReal_real_eq_id]

theorem uniLat_det_le_of_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {G H : Matrix ι ι ℝ}
    (hG : G.PosDef) (hGH : (H - G).PosSemidef) : G.det ≤ H.det := by
  set Q := H - G with hQdef
  have hH : H = G + Q := by rw [hQdef]; abel
  have hs := hG.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at hs
  set U := hG.1.eigenvectorUnitary with hU
  set ev := hG.1.eigenvalues with hev
  have hpos : ∀ i, 0 < ev i := hG.eigenvalues_pos
  set D : Matrix ι ι ℝ := diagonal (fun i => (Real.sqrt (ev i))⁻¹) with hD
  set C : Matrix ι ι ℝ := D * star (U : Matrix ι ι ℝ) with hC
  have hUU' : star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ) = 1 := Unitary.coe_star_mul_self U
  have hCt : Cᴴ = (U : Matrix ι ι ℝ) * D := by
    rw [hC, conjTranspose_mul, ← star_eq_conjTranspose, star_star, hD, diagonal_conjTranspose]
    congr 2

  have hCG : C * G * Cᴴ = 1 := by
    rw [hCt, hC]
    conv_lhs => rw [hs]
    have e : D * star (U : Matrix ι ι ℝ) * ((U : Matrix ι ι ℝ) * diagonal ev * star (U : Matrix ι ι ℝ))
        * ((U : Matrix ι ι ℝ) * D)
        = D * (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)) * diagonal ev
          * (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)) * D := by
      simp only [Matrix.mul_assoc]
    rw [e, hUU', Matrix.mul_one, Matrix.mul_one, hD, diagonal_mul_diagonal, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext i
    have h1 := Real.mul_self_sqrt (hpos i).le
    have h2 : Real.sqrt (ev i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
    field_simp
    linarith
  have hQ' : (C * Q * Cᴴ).PosSemidef := by
    have := hGH.conjTranspose_mul_mul_same Cᴴ
    rwa [conjTranspose_conjTranspose] at this
  have hCH : C * H * Cᴴ = 1 + C * Q * Cᴴ := by
    rw [hH, Matrix.mul_add, Matrix.add_mul, hCG]
  have h1 : 1 ≤ (C * H * Cᴴ).det := by
    rw [hCH, uniLat_det_one_add hQ']
    calc (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun i _ => by linarith [hQ'.eigenvalues_nonneg i])
  have h2 : (C * G * Cᴴ).det = 1 := by rw [hCG, det_one]
  rw [det_mul, det_mul, det_conjTranspose, star_trivial] at h1 h2
  have hc : C.det ≠ 0 := by
    intro h0; rw [h0] at h2; simp at h2
  have hc2 : 0 < C.det * C.det := mul_self_pos.mpr hc
  have : G.det * (C.det * C.det) ≤ H.det * (C.det * C.det) := by nlinarith
  exact le_of_mul_le_mul_right this hc2

end ReciprocityTheory.L2DbarEstimates.Y
