import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFsPotLaplacian
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Real MeasureTheory Filter Topology Set

theorem hasFDerivAt_fsPotPlane (z : ℂ) :
    HasFDerivAt fsPotPlane ((1 + ‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z := by
  have hl : HasFDerivAt (fun y : ℂ => Real.log (1 + ‖y‖ ^ 2))
      ((1 + ‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z)) z :=
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add 1).log (by positivity)
  have e : fsPotPlane = fun y : ℂ => Real.log (1 + ‖y‖ ^ 2) * (1 / 2) := by
    funext y; simp only [fsPotPlane]; ring
  rw [e]
  refine (hl.mul_const (1 / 2 : ℝ)).congr_fderiv ?_
  ext w
  simp
  ring

theorem fderiv_fsPotPlane_apply (z e : ℂ) :
    fderiv ℝ fsPotPlane z e = (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im) := by
  rw [(hasFDerivAt_fsPotPlane z).fderiv]
  simp [Complex.inner] <;> ring_nf <;> simp

theorem fderiv_fderiv_fsPotPlane_apply (y e : ℂ) :
    fderiv ℝ (fderiv ℝ fsPotPlane) y e e =
      fderiv ℝ (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im)) y e := by
  have hd : DifferentiableAt ℝ (fderiv ℝ fsPotPlane) y :=
    ((contDiff_fsPotPlane.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) y
  have h := fderiv_clm_apply hd (differentiableAt_const e)
  have hfun : (fun z : ℂ => fderiv ℝ fsPotPlane z e) =
      fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im) :=
    funext fun z => fderiv_fsPotPlane_apply z e
  rw [hfun] at h
  rw [h]
  simp

theorem hasFDerivAt_partial (y e : ℂ) :
    HasFDerivAt (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im))
      ((1 + ‖y‖ ^ 2)⁻¹ • (e.re • Complex.reCLM + e.im • Complex.imCLM) +
        (y.re * e.re + y.im * e.im) •
          (-(((1 + ‖y‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ y))) y := by
  have h1 : HasFDerivAt (fun z : ℂ => 1 + ‖z‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_add 1
  have h2 : HasFDerivAt (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-((1 + ‖y‖ ^ 2) ^ 2)⁻¹)).comp
        (2 • innerSL ℝ y)) y :=
    (hasFDerivAt_inv (by positivity : (1 + ‖y‖ ^ 2) ≠ 0)).comp y h1
  have h3 : HasFDerivAt (fun z : ℂ => z.re * e.re + z.im * e.im)
      (e.re • Complex.reCLM + e.im • Complex.imCLM) y := by
    have hf : (fun z : ℂ => z.re * e.re + z.im * e.im) =
        fun z => (e.re • Complex.reCLM + e.im • Complex.imCLM) z := by
      funext z; simp; ring
    rw [hf]
    exact ContinuousLinearMap.hasFDerivAt _
  refine (h2.mul h3).congr_fderiv ?_
  ext w
  simp <;> ring_nf <;> simp

theorem laplacian_fsPotPlane (y : ℂ) : Δ fsPotPlane y = 2 / (1 + ‖y‖ ^ 2) ^ 2 := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_fderiv_fsPotPlane_apply, fderiv_fderiv_fsPotPlane_apply,
    (hasFDerivAt_partial y 1).fderiv, (hasFDerivAt_partial y Complex.I).fderiv]
  have hn : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hp : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  simp [Complex.inner]
  rw [hn] at hp ⊢
  field_simp
  ring

theorem integrable_laplacian_fsPotPlane : Integrable (Δ fsPotPlane) := by
  have h : Δ fsPotPlane = fun y : ℂ => 2 * ((1 : ℝ) + ‖y‖ ^ 2) ^ (-(4 : ℝ) / 2) := by
    funext y
    rw [laplacian_fsPotPlane, show -(4 : ℝ) / 2 = -((2 : ℕ) : ℝ) by norm_num,
      rpow_neg (by positivity), rpow_natCast, div_eq_mul_inv]
  rw [h]
  exact (integrable_rpow_neg_one_add_norm_sq (by simp [Complex.finrank_real_complex]; norm_num)).const_mul 2

theorem integral_radial_fsPot :
    ∫ s in Ioi (0 : ℝ), s ^ (2 - 1) • (2 / (1 + s ^ 2) ^ 2) = 1 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun s : ℝ => -(1 + s ^ 2)⁻¹)
      (x ^ (2 - 1) • (2 / (1 + x ^ 2) ^ 2)) x := by
    intro x _
    have hx : (1 + x ^ 2) ≠ 0 := by positivity
    have h := (((hasDerivAt_pow 2 x).const_add 1).inv hx).neg
    refine h.congr_deriv ?_
    rw [smul_eq_mul, neg_div, neg_neg]
    push_cast
    ring
  have htend : Tendsto (fun s : ℝ => -(1 + s ^ 2)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => 1 + s ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
    simpa using h.inv_tendsto_atTop.neg
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx => by
    have : (0 : ℝ) < x := hx
    positivity) htend
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
  norm_num

theorem integral_laplacian_fsPotPlane : ∫ y, Δ fsPotPlane y = 2 * π := by
  have h : (fun y : ℂ => Δ fsPotPlane y) = fun y : ℂ => (fun s : ℝ => 2 / (1 + s ^ 2) ^ 2) ‖y‖ :=
    funext laplacian_fsPotPlane
  rw [h, integral_fun_norm_addHaar volume (fun s : ℝ => 2 / (1 + s ^ 2) ^ 2),
    Complex.finrank_real_complex, integral_radial_fsPot]
  simp [Measure.real, Complex.volume_ball]

theorem FsPotLaplacian.proof : FsPotLaplacian.Statement :=
  ⟨laplacian_fsPotPlane, integrable_laplacian_fsPotPlane, integral_laplacian_fsPotPlane⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
