import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCDet

open Matrix
open scoped MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

theorem det_eq_ofReal_re {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A.det = (RCLike.re A.det : 𝕜) := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]

theorem re_det_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) : 0 ≤ RCLike.re A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]
  exact Finset.prod_nonneg fun i _ => hA.eigenvalues_nonneg i

theorem re_det_pos {A : Matrix n n 𝕜} (hA : A.PosDef) : 0 < RCLike.re A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]
  exact Finset.prod_pos fun i _ => hA.eigenvalues_pos i

theorem one_le_re_det_one_add {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) :
    1 ≤ RCLike.re (1 + Q).det := by
  have hspec := hQ.isHermitian.spectral_theorem
  set U := hQ.isHermitian.eigenvectorUnitary
  have hUU : (U : Matrix n n 𝕜) * star (U : Matrix n n 𝕜) = 1 := Unitary.coe_mul_star_self U
  have h1 : 1 + Q = (U : Matrix n n 𝕜) *
      ((1 : Matrix n n 𝕜) + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)) *
        star (U : Matrix n n 𝕜) := by
    conv_lhs => rw [hspec]
    rw [Unitary.conjStarAlgAut_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU]
  have hdet : (1 + Q).det =
      ((1 : Matrix n n 𝕜) + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)).det := by
    rw [h1, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      Unitary.coe_star_mul_self, det_one, one_mul]
  rw [hdet, ← diagonal_one, diagonal_add, det_diagonal]
  have : ∏ i, ((1 : 𝕜) + (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues) i) =
      ((∏ i, (1 + hQ.isHermitian.eigenvalues i) : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  rw [this, RCLike.ofReal_re]
  exact Finset.one_le_prod fun i _ => by linarith [hQ.eigenvalues_nonneg i]

theorem re_det_le_re_det_add {A P : Matrix n n 𝕜} (hA : A.PosSemidef) (hP : P.PosSemidef) :
    RCLike.re A.det ≤ RCLike.re (A + P).det := by
  by_cases h0 : A.det = 0
  · rw [h0, map_zero]
    exact re_det_nonneg (hA.add hP)
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [star_eq_conjTranspose] at hB
  have hBdet : B.det ≠ 0 := by
    intro hb
    apply h0
    rw [hB, det_mul, hb, mul_zero]
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hBHu : IsUnit Bᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hBdet)
  set Q := (B⁻¹)ᴴ * P * B⁻¹ with hQdef
  have hQ : Q.PosSemidef := by
    have := hP.mul_mul_conjTranspose_same ((B⁻¹)ᴴ)
    simpa [hQdef, conjTranspose_conjTranspose] using this
  have hAP : A + P = Bᴴ * (1 + Q) * B := by
    rw [hQdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hB]
    congr 1
    rw [conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hBHu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBu, Matrix.mul_one]
  have hdet : (A + P).det = A.det * (1 + Q).det := by
    rw [hAP, hB, det_mul, det_mul, det_mul]
    ring
  have h1 := one_le_re_det_one_add hQ
  have h2 := re_det_nonneg hA
  obtain ⟨a, ha⟩ : ∃ a : ℝ, A.det = a := ⟨_, det_eq_ofReal_re hA⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, (1 + Q).det = b := ⟨_, det_eq_ofReal_re (PosSemidef.one.add hQ)⟩
  rw [hdet, ha, hb, ← RCLike.ofReal_mul]
  simp only [RCLike.ofReal_re]
  rw [ha, RCLike.ofReal_re] at h2
  rw [hb, RCLike.ofReal_re] at h1
  nlinarith

theorem re_det_mono {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) :
    RCLike.re A.det ≤ RCLike.re B.det := by
  have := re_det_le_re_det_add hA hAB
  rwa [add_sub_cancel] at this

theorem log_re_det_le {A : Matrix n n 𝕜} (hA : A.PosDef) :
    Real.log (RCLike.re A.det) ≤ RCLike.re A.trace - Fintype.card n := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues,
    ← RCLike.ofReal_prod, ← RCLike.ofReal_sum, RCLike.ofReal_re, RCLike.ofReal_re,
    Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')]
  have : (Fintype.card n : ℝ) = ∑ _i : n, (1 : ℝ) := by simp
  rw [this, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)

theorem norm_det_mul_sq_le (A B : Matrix m n 𝕜) :
    ‖(Bᴴ * A).det‖ ^ 2 ≤ RCLike.re (Bᴴ * B).det * RCLike.re (Aᴴ * A).det := by
  have hG := posSemidef_conjTranspose_mul_self A
  have hBB := posSemidef_conjTranspose_mul_self B
  by_cases h0 : (Aᴴ * A).det = 0
  · obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have hAx : A *ᵥ x = 0 := by
      have h := congrArg (fun v => star x ⬝ᵥ v) hx
      simp only [dotProduct_zero] at h
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose] at h
      simp only [star_star] at h
      exact dotProduct_star_self_eq_zero.mp h
    have hC : (Bᴴ * A).det = 0 :=
      exists_mulVec_eq_zero_iff.mp ⟨x, hx0, by rw [← mulVec_mulVec, hAx, mulVec_zero]⟩
    rw [hC, h0, norm_zero, map_zero]
    simp
  · have hGpd : (Aᴴ * A).PosDef := hG.posDef_iff_det_ne_zero.mpr h0
    set G := Aᴴ * A with hGdef
    set C := Bᴴ * A with hCdef
    have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr h0
    have hGiG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
    have hGiH : (G⁻¹)ᴴ = G⁻¹ := by
      rw [conjTranspose_nonsing_inv, hGpd.isHermitian.eq]
    have hCH : Cᴴ = Aᴴ * B := by
      rw [hCdef, conjTranspose_mul, conjTranspose_conjTranspose]
    set E := B - A * (G⁻¹ * Cᴴ) with hEdef
    have hcancel : ∀ Z : Matrix n n 𝕜, G⁻¹ * (Aᴴ * (A * Z)) = Z := by
      intro Z
      rw [← Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc, ← hGdef, hGiG, Matrix.one_mul]
    have hEE : Bᴴ * B = C * G⁻¹ * Cᴴ + Eᴴ * E := by
      rw [hEdef, hCH]
      simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hGiH]
      rw [hCdef]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hcancel]
      abel
    have hPSD1 : (C * G⁻¹ * Cᴴ).PosSemidef := hGpd.inv.posSemidef.mul_mul_conjTranspose_same C
    have hPSD2 : (Eᴴ * E).PosSemidef := posSemidef_conjTranspose_mul_self E
    have hle := re_det_le_re_det_add hPSD1 hPSD2
    rw [← hEE] at hle
    have hg := re_det_pos hGpd
    have hdetC : (C * G⁻¹ * Cᴴ).det = ((‖C.det‖ ^ 2 * (RCLike.re G.det)⁻¹ : ℝ) : 𝕜) := by
      rw [det_mul, det_mul, det_conjTranspose, det_nonsing_inv, Ring.inverse_eq_inv',
        det_eq_ofReal_re hG, mul_comm (C.det), mul_assoc, RCLike.star_def, RCLike.mul_conj]
      push_cast
      ring
    rw [hdetC, RCLike.ofReal_re] at hle
    rw [← div_eq_mul_inv, div_le_iff₀ hg] at hle
    exact hle

theorem norm_det_mul_sq_le_of_posDef [DecidableEq m] {M : Matrix m m 𝕜} (hM : M.PosDef)
    (F W : Matrix m n 𝕜) :
    ‖(Wᴴ * F).det‖ ^ 2 ≤ RCLike.re (Wᴴ * M * W).det * RCLike.re (Fᴴ * M⁻¹ * F).det := by
  obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hL
  have hLdet : L.det ≠ 0 := by
    intro hl
    have := hM.det_pos.ne'
    rw [hL, det_mul, hl, mul_zero] at this
    exact this rfl
  have hLu : IsUnit L.det := isUnit_iff_ne_zero.mpr hLdet
  have hLHu : IsUnit Lᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hLdet)
  have h := norm_det_mul_sq_le ((Lᴴ)⁻¹ * F) (L * W)
  have e1 : (L * W)ᴴ * ((Lᴴ)⁻¹ * F) = Wᴴ * F := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Lᴴ,
      Matrix.mul_nonsing_inv _ hLHu, Matrix.one_mul]
  have e2 : (L * W)ᴴ * (L * W) = Wᴴ * M * W := by
    rw [conjTranspose_mul, hL, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  have e3 : ((Lᴴ)⁻¹ * F)ᴴ * ((Lᴴ)⁻¹ * F) = Fᴴ * M⁻¹ * F := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_conjTranspose, hL,
      Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc L⁻¹]
  rw [e1, e2, e3] at h
  exact h

end GroundTheory.Heights₂.Heights.MCDet
