import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0

open scoped BigOperators ComplexOrder
open Finset Matrix

theorem psd_det_re_le_one_of_diag (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosSemidef)
    (hd : ∀ c, H c c = 1) : H.det.re ≤ 1 := by
  have hHerm := hH.isHermitian
  have htr : ∑ i, hHerm.eigenvalues i = N := by
    have h := hHerm.trace_eq_sum_eigenvalues
    have h2 : H.trace = N := by simp [Matrix.trace, hd]
    rw [h2] at h
    have h4 := congrArg (RCLike.re : ℂ → ℝ) h
    simp only [map_sum, RCLike.ofReal_re, RCLike.natCast_re] at h4
    linarith
  have hre : H.det.re = ∏ i, hHerm.eigenvalues i := by
    rw [hHerm.det_eq_prod_eigenvalues]
    first
      | (norm_cast)
      | simp [← Complex.ofReal_prod]
  rw [hre]
  calc ∏ i, hHerm.eigenvalues i ≤ ∏ i, Real.exp (hHerm.eigenvalues i - 1) :=
        Finset.prod_le_prod (fun i _ => hH.eigenvalues_nonneg i)
          (fun i _ => by linarith [Real.add_one_le_exp (hHerm.eigenvalues i - 1)])
    _ = Real.exp (∑ i, (hHerm.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
    _ = 1 := by simp [Finset.sum_sub_distrib, htr]

theorem psd_det_re_le_prod_diag (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosSemidef) :
    G.det.re ≤ ∏ c, (G c c).re := by
  classical
  have hdiag : ∀ c, G c c = ((G c c).re : ℂ) := fun c =>
    (Complex.conj_eq_iff_re.mp (by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hG.1 c) c)).symm
  have hnn : ∀ c, 0 ≤ (G c c).re := fun c => (Complex.nonneg_iff.mp (hG.diag_nonneg (i := c))).1
  by_cases hz : ∃ c, (G c c).re = 0
  · obtain ⟨c, hc⟩ := hz
    have hcol : G *ᵥ Pi.single c 1 = 0 := by
      rw [← hG.dotProduct_mulVec_zero_iff]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hdiag c, hc]
      simp
    have hdet : G.det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero c
      intro i
      have h := congrFun hcol i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
    rw [hdet, Complex.zero_re]
    exact Finset.prod_nonneg fun c _ => hnn c
  · push_neg at hz
    have hpos : ∀ c, 0 < (G c c).re := fun c => lt_of_le_of_ne (hnn c) (Ne.symm (hz c))
    set d : Fin N → ℝ := fun c => (Real.sqrt (G c c).re)⁻¹ with hd_def
    have hdr : ∀ c, d c * (G c c).re * d c = 1 := fun c => by
      have hs := Real.mul_self_sqrt (hnn c)
      have hsq : Real.sqrt (G c c).re ≠ 0 := (Real.sqrt_pos.mpr (hpos c)).ne'
      simp only [hd_def]
      field_simp
      nlinarith [hs]
    set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal fun c => (d c : ℂ) with hD_def
    have hD : Dᴴ = D := by simp [hD_def, Matrix.diagonal_conjTranspose]
    have hH : (D * G * D).PosSemidef := by
      have h := hG.conjTranspose_mul_mul_same D
      rwa [hD] at h
    have hHd : ∀ c, (D * G * D) c c = 1 := by
      intro c
      simp only [hD_def, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rw [hdiag c]
      exact_mod_cast hdr c
    have h1 := psd_det_re_le_one_of_diag N _ hH hHd
    have hdet : (D * G * D).det = (((∏ c, d c) ^ 2 : ℝ) : ℂ) * G.det := by
      simp only [hD_def, Matrix.det_mul, Matrix.det_diagonal]
      push_cast
      ring
    rw [hdet, Complex.re_ofReal_mul] at h1
    have hprod : (∏ c, d c) ^ 2 * ∏ c, (G c c).re = 1 := by
      rw [show (∏ c, d c) ^ 2 * ∏ c, (G c c).re = ∏ c, (d c * (G c c).re * d c) by
        rw [sq, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun c _ => by ring]
      exact Finset.prod_eq_one fun c _ => hdr c
    have hp : 0 < (∏ c, d c) ^ 2 :=
      pow_pos (Finset.prod_pos fun c _ => inv_pos.mpr (Real.sqrt_pos.mpr (hpos c))) 2
    by_contra hlt
    push_neg at hlt
    have := mul_lt_mul_of_pos_left hlt hp
    linarith

theorem hadamard_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by
  have hdet : (A * Aᴴ).det.re = ‖A.det‖ ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    rw [show star A.det = (starRingEnd ℂ) A.det from rfl, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hdiag : ∀ i, ((A * Aᴴ) i i).re = ∑ j, ‖A i j‖ ^ 2 := fun i => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show star (A i j) = (starRingEnd ℂ) (A i j) from rfl, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have key := psd_det_re_le_prod_diag n (A * Aᴴ) (Matrix.posSemidef_self_mul_conjTranspose A)
  rw [hdet] at key
  simp only [hdiag] at key
  have hs : ∀ i, 0 ≤ ∑ j, ‖A i j‖ ^ 2 := fun i => Finset.sum_nonneg fun j _ => by positivity
  calc ‖A.det‖ = Real.sqrt (‖A.det‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [← Finset.prod_pow]
        have h : ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) ^ 2 = ∏ i, ∑ j, ‖A i j‖ ^ 2 :=
          Finset.prod_congr rfl fun i _ => Real.sq_sqrt (hs i)
        rw [h]
        exact key
    _ = ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) :=
        Real.sqrt_sq (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _)

end ReciprocityTheory.ChartRestriction.G.T0
