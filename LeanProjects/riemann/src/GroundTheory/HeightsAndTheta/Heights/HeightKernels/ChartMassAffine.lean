import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory

noncomputable section

namespace ChartMongeAmpereAffineInvariance

variable {D : ℕ}

def sesq (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (u v : Fin D → ℂ) : ℂ :=
  ((H u v + H (Complex.I • u) (Complex.I • v) : ℝ) +
    Complex.I * ((H u (Complex.I • v) - H (Complex.I • u) v : ℝ))) / 4

theorem cxHessian_eq_sesq (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (i j : Fin D) :
    cxHessian f z i j = sesq (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := rfl

section Sesq

variable (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)

theorem sesq_add_left (u u' v : Fin D → ℂ) : sesq H (u + u') v = sesq H u v + sesq H u' v := by
  simp only [sesq, smul_add, map_add, _root_.add_apply]
  push_cast
  ring

theorem sesq_add_right (u v v' : Fin D → ℂ) : sesq H u (v + v') = sesq H u v + sesq H u v' := by
  simp only [sesq, smul_add, map_add]
  push_cast
  ring

theorem sesq_real_smul_left (r : ℝ) (u v : Fin D → ℂ) : sesq H (r • u) v = r * sesq H u v := by
  simp only [sesq, smul_comm Complex.I r u, map_smul, _root_.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem sesq_real_smul_right (r : ℝ) (u v : Fin D → ℂ) : sesq H u (r • v) = r * sesq H u v := by
  simp only [sesq, smul_comm Complex.I r v, map_smul, smul_eq_mul]
  push_cast
  ring

theorem sesq_I_left (u v : Fin D → ℂ) : sesq H (Complex.I • u) v = Complex.I * sesq H u v := by
  have h : Complex.I • Complex.I • u = -u := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [sesq, h, map_neg, _root_.neg_apply]
  push_cast
  linear_combination (-(H u (Complex.I • v) : ℂ) + (H (Complex.I • u) v : ℂ)) / 4 * Complex.I_sq

theorem sesq_I_right (u v : Fin D → ℂ) : sesq H u (Complex.I • v) = -Complex.I * sesq H u v := by
  have h : Complex.I • Complex.I • v = -v := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [sesq, h, map_neg]
  push_cast
  linear_combination ((H u (Complex.I • v) : ℂ) - (H (Complex.I • u) v : ℂ)) / 4 * Complex.I_sq

theorem smul_eq_re_add_im (a : ℂ) (u : Fin D → ℂ) : a • u = a.re • u + a.im • (Complex.I • u) := by
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  conv_lhs => rw [← Complex.re_add_im a]
  ring

theorem sesq_smul_left (a : ℂ) (u v : Fin D → ℂ) : sesq H (a • u) v = a * sesq H u v := by
  rw [smul_eq_re_add_im, sesq_add_left, sesq_real_smul_left, sesq_real_smul_left, sesq_I_left]
  conv_rhs => rw [← Complex.re_add_im a]
  ring

theorem sesq_smul_right (a : ℂ) (u v : Fin D → ℂ) : sesq H u (a • v) = star a * sesq H u v := by
  rw [smul_eq_re_add_im, sesq_add_right, sesq_real_smul_right, sesq_real_smul_right, sesq_I_right]
  have hs : star a = (a.re : ℂ) - a.im * Complex.I := by apply Complex.ext <;> simp
  rw [hs]
  ring

theorem sesq_sum_left (u : Fin D → Fin D → ℂ) (v : Fin D → ℂ) :
    sesq H (∑ k, u k) v = ∑ k, sesq H (u k) v :=
  map_sum (AddMonoidHom.mk' (fun a => sesq H a v) fun a b => sesq_add_left H a b v) u Finset.univ

theorem sesq_sum_right (u : Fin D → ℂ) (v : Fin D → Fin D → ℂ) :
    sesq H u (∑ l, v l) = ∑ l, sesq H u (v l) :=
  map_sum (AddMonoidHom.mk' (fun b => sesq H u b) fun a b => sesq_add_right H u a b) v Finset.univ

theorem eq_sum_smul_single (a : Fin D → ℂ) : a = ∑ k, a k • (Pi.single k 1 : Fin D → ℂ) := by
  funext p
  simp [Finset.sum_apply, Pi.single_apply]

theorem sesq_expand (a b : Fin D → ℂ) :
    sesq H a b = ∑ k, ∑ l, a k * star (b l) * sesq H (Pi.single k 1) (Pi.single l 1) := by
  conv_lhs => rw [eq_sum_smul_single a, eq_sum_smul_single b]
  rw [sesq_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sesq_sum_right]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sesq_smul_left, sesq_smul_right]
  ring

end Sesq

def realCLE (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ) :=
  letI := P.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hP)
  ((P.toLinearEquiv' this).restrictScalars ℝ).toContinuousLinearEquiv

theorem realCLE_apply (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) (y : Fin D → ℂ) :
    realCLE P hP y = P *ᵥ y := rfl

theorem fderiv_fderiv_comp_affine (φ : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (L : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ))
    (κ : ℝ) (z u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ fun y => φ (c + L y) + κ) z u v = fderiv ℝ (fderiv ℝ φ) (c + L z) (L u) (L v) := by
  have h1 : (fderiv ℝ fun y => φ (c + L y) + κ) =
      fun y => (fderiv ℝ φ (c + L y)).comp (L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) := by
    funext y
    rw [fderiv_add_const]
    have : (fun y => φ (c + L y)) = (fun w => φ (c + w)) ∘ L := rfl
    rw [this, L.comp_right_fderiv, fderiv_comp_add_left]
  have h2 : (fun y => (fderiv ℝ φ (c + L y)).comp (L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ))) =
      (L.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) ∘ ((fun w => fderiv ℝ φ (c + w)) ∘ L) := by
    funext y
    ext w
    simp [ContinuousLinearEquiv.arrowCongr_apply]
  rw [h1, h2, ContinuousLinearEquiv.comp_fderiv, L.comp_right_fderiv, fderiv_comp_add_left]
  simp [ContinuousLinearEquiv.arrowCongr_apply]

theorem cxHessian_comp_affine (φ : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    cxHessian (fun y => φ (c + P *ᵥ y) + κ) z =
      Pᵀ * cxHessian φ (c + P *ᵥ z) * P.map (starRingEnd ℂ) := by
  ext i j
  set L := realCLE P hP
  set H := fderiv ℝ (fderiv ℝ φ) (c + P *ᵥ z)
  have hI : ∀ w, L (Complex.I • w) = Complex.I • L w := fun w => by
    simp only [L, realCLE_apply, Matrix.mulVec_smul]
  have hent : cxHessian (fun y => φ (c + P *ᵥ y) + κ) z i j = sesq H (L (Pi.single i 1)) (L (Pi.single j 1)) := by
    have hg : (fun y => φ (c + P *ᵥ y) + κ) = fun y => φ (c + L y) + κ := rfl
    rw [cxHessian_eq_sesq, hg]
    simp only [sesq, fderiv_fderiv_comp_affine, hI]
    rfl
  rw [hent, sesq_expand]
  simp only [L, realCLE_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    mulVec_single_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hc : cxHessian φ (c + P *ᵥ z) l k = sesq H (Pi.single l 1) (Pi.single k 1) := rfl
  simp only [Matrix.col_apply, starRingEnd_apply, hc]
  ring

theorem mixedDisc_mul_mul (P Q : Matrix (Fin D) (Fin D) ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => P * A k * Q) = P.det * Q.det * mixedDisc A := by
  have hS : ∀ S : Finset (Fin D), (∑ k ∈ S, P * A k * Q) = P * (∑ k ∈ S, A k) * Q := fun S => by
    rw [Finset.mul_sum, Finset.sum_mul]
  simp only [mixedDisc, hS, det_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  ring

theorem maDensity_comp_affine (φ : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    maDensity (fun _ : Fin D => fun y => φ (c + P *ᵥ y) + κ) z =
      Complex.normSq P.det * maDensity (fun _ : Fin D => φ) (c + P *ᵥ z) := by
  have hQ : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
  simp only [maDensity, cxHessian_comp_affine φ c P hP κ z]
  rw [mixedDisc_mul_mul (Pᵀ) (P.map (starRingEnd ℂ)) (fun _ => cxHessian φ (c + P *ᵥ z)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring

theorem det_realCLE (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) :
    LinearMap.det ((realCLE P hP : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      Complex.normSq P.det := by
  have h : ((realCLE P hP : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      (Matrix.toLin' P).restrictScalars ℝ := by
    ext y
    simp [realCLE_apply]
  rw [h, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]

theorem integral_comp_affine (f : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.det ≠ 0) :
    ∫ y, f (c + P *ᵥ y) = (Complex.normSq P.det)⁻¹ * ∫ y, f y := by
  set L := realCLE P hP
  have hpos : 0 < Complex.normSq P.det := Complex.normSq_pos.mpr hP
  have hdet := det_realCLE P hP
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin D → ℂ))
    (f := ((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ))) (by rw [hdet]; exact hpos.ne')
  have hcoe : ⇑((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) = ⇑L := rfl
  rw [hcoe, hdet] at hmap
  calc ∫ y, f (c + P *ᵥ y) = ∫ y, (fun w => f (c + w)) (L y) := rfl
    _ = ∫ w, f (c + w) ∂(Measure.map L volume) :=
        (L.toHomeomorph.measurableEmbedding.integral_map (fun w => f (c + w))).symm
    _ = (Complex.normSq P.det)⁻¹ * ∫ y, f y := by
        rw [hmap, integral_smul_measure, integral_add_left_eq_self, ENNReal.toReal_ofReal (abs_nonneg _),
          abs_inv, abs_of_pos hpos, smul_eq_mul]

end ChartMongeAmpereAffineInvariance

end

end GroundTheory.Heights₂.Heights
