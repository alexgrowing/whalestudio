import Mathlib

namespace GlobalTheory

open Complex

theorem logNormSq_coord_fderiv_sq_add_sq :
    ∀ {e : ℕ} (k : Fin e) (z : Fin e → ℂ), z k ≠ 0 →
      DifferentiableAt ℝ (fun y : Fin e → ℂ => Real.log (‖y k‖ ^ 2)) z ∧
      ∀ w : Fin e → ℂ,
        (fderiv ℝ (fun y : Fin e → ℂ => Real.log (‖y k‖ ^ 2)) z w) ^ 2 +
          (fderiv ℝ (fun y : Fin e → ℂ => Real.log (‖y k‖ ^ 2)) z (Complex.I • w)) ^ 2 =
            4 * ‖w k‖ ^ 2 / ‖z k‖ ^ 2 := by
  intro e k z hz
  let p : (Fin e → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj k
  have h1 : HasFDerivAt (fun y : Fin e → ℂ => ‖y k‖ ^ 2) (2 • (innerSL ℝ (z k)).comp p) z := by
    have := (p.hasFDerivAt (x := z)).norm_sq
    simpa [p] using this
  have h0 : ‖z k‖ ^ 2 ≠ 0 := by positivity
  have h2 := h1.log h0
  refine ⟨h2.differentiableAt, fun w => ?_⟩
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    smul_eq_mul, p, ContinuousLinearMap.proj_apply, Pi.smul_apply, Complex.inner]
  have hn : ‖z k‖ ^ 2 = (z k).re ^ 2 + (z k).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hw : ‖w k‖ ^ 2 = (w k).re ^ 2 + (w k).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hpos : (z k).re ^ 2 + (z k).im ^ 2 ≠ 0 := by rw [← hn]; exact h0
  rw [hn, hw]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.mul_im, Complex.smul_re, Complex.smul_im]
  field_simp
  simp only [nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory
