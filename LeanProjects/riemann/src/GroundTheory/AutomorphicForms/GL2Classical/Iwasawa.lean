import Mathlib

open Matrix UpperHalfPlane

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

theorem det_fin_two_kmat (w : ℂ) : (!![w.re, -w.im; w.im, w.re] : Matrix (Fin 2) (Fin 2) ℝ).det =
    Complex.normSq w := by
  rw [Matrix.det_fin_two_of, Complex.normSq_apply]
  ring

def kGL (w : ℂ) (hw : w ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![w.re, -w.im; w.im, w.re] (by
    rw [det_fin_two_kmat]
    exact (Complex.normSq_pos.2 hw).ne')

@[simp]
theorem coe_kGL (w : ℂ) (hw : w ≠ 0) :
    (kGL w hw : Matrix (Fin 2) (Fin 2) ℝ) = !![w.re, -w.im; w.im, w.re] :=
  rfl

theorem det_kGL (w : ℂ) (hw : w ≠ 0) : (kGL w hw).det.val = Complex.normSq w := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_kGL, det_fin_two_kmat]

theorem det_kGL_pos (w : ℂ) (hw : w ≠ 0) : 0 < (kGL w hw).det.val := by
  rw [det_kGL]
  exact Complex.normSq_pos.2 hw

theorem denom_kGL (w : ℂ) (hw : w ≠ 0) : denom (kGL w hw) (I : ℂ) = w := by
  rw [denom]
  apply Complex.ext <;> simp

theorem kGL_smul_I (w : ℂ) (hw : w ≠ 0) : kGL w hw • I = I := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_kGL_pos w hw), denom_kGL, div_eq_iff hw]
  rw [num]
  apply Complex.ext <;> simp

theorem kGL_mul (w₁ w₂ : ℂ) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) :
    kGL w₁ hw₁ * kGL w₂ hw₂ = kGL (w₁ * w₂) (mul_ne_zero hw₁ hw₂) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, coe_kGL, coe_kGL, coe_kGL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def borelGL (z : ℍ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![z.im, z.re; 0, 1] (by
    rw [Matrix.det_fin_two_of]
    simpa using z.im_pos.ne')

@[simp]
theorem coe_borelGL (z : ℍ) :
    (borelGL z : Matrix (Fin 2) (Fin 2) ℝ) = !![z.im, z.re; 0, 1] :=
  rfl

theorem det_borelGL (z : ℍ) : (borelGL z).det.val = z.im := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_borelGL, Matrix.det_fin_two_of]
  ring

theorem det_borelGL_pos (z : ℍ) : 0 < (borelGL z).det.val := by
  rw [det_borelGL]
  exact z.im_pos

theorem denom_borelGL (z : ℍ) (w : ℂ) : denom (borelGL z) w = 1 := by
  simp [denom]

theorem borelGL_smul_I (z : ℍ) : borelGL z • I = z := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_borelGL_pos z), denom_borelGL, div_one, num]
  apply Complex.ext <;> simp

theorem re_smul_I {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    (h • I).re = ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * h 1 0 + h 0 1 * h 1 1) /
      Complex.normSq (denom h (I : ℂ)) := by
  rw [UpperHalfPlane.re, coe_smul_of_det_pos hpos, Complex.div_re]
  simp only [num, denom, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, coe_I, Complex.I_re, Complex.I_im]
  ring

theorem im_smul_I {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    (h • I).im = h.det.val / Complex.normSq (denom h (I : ℂ)) := by
  rw [im_smul_eq_div_normSq, abs_of_pos hpos, I_im, mul_one]

theorem eq_borelGL_mul_kGL {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    h = borelGL (h • I) * kGL (denom h (I : ℂ)) (denom_ne_zero h I) := by
  have hN : Complex.normSq (denom h (I : ℂ)) ≠ 0 :=
    (Complex.normSq_pos.2 (denom_ne_zero h I)).ne'
  have hN' : Complex.normSq (denom h (I : ℂ)) = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + h 1 1 ^ 2 := by
    simp [denom, Complex.normSq_apply]
    ring
  have hdet : h.det.val = (h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hre := re_smul_I hpos
  have him := im_smul_I hpos
  rw [hN'] at hre him
  have hD : (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + h 1 1 ^ 2 ≠ 0 := hN' ▸ hN
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, coe_borelGL, coe_kGL]
  have hdr : (denom h (I : ℂ)).re = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by simp [denom]
  have hdi : (denom h (I : ℂ)).im = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by simp [denom]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, hdr, hdi, hre, him, hdet] <;>
    field_simp <;> ring

end GL2Classical

end

end GroundTheory.Automorphic
