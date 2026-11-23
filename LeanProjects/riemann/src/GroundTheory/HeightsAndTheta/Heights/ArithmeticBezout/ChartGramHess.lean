import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open scoped InnerProductSpace
open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem ChartGram.hasFDerivAt_re_inner {u w : E → F} {y : E} {u' w' : E →L[ℝ] F}
    (hu : HasFDerivAt u u' y) (hw : HasFDerivAt w w' y) :
    HasFDerivAt (fun y' => (⟪u y', w y'⟫_ℂ).re)
      (Complex.reCLM.comp ((fderivInnerCLM ℂ (u y, w y)).comp (u'.prod w'))) y :=
  Complex.reCLM.hasFDerivAt.comp y (HasFDerivAt.inner ℂ hu hw)

theorem ChartGram.re_inner_self_pos {x : F} (h0 : x ≠ 0) : 0 < (⟪x, x⟫_ℂ).re := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) x
  have h' : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := h
  rw [h']; positivity

theorem ChartGram.re_inner_comm (x z : F) : (⟪x, z⟫_ℂ).re = (⟪z, x⟫_ℂ).re := by
  rw [← inner_conj_symm x z, Complex.conj_re]

theorem ChartGram.fderiv_half_log_apply {u : E → F} {y : E}
    (hu : DifferentiableAt ℂ u y) (h0 : u y ≠ 0) (b : E) :
    fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y b =
      (⟪u y, fderiv ℂ u y b⟫_ℂ).re * ((⟪u y, u y⟫_ℂ).re)⁻¹ := by
  have h1 : HasFDerivAt u ((fderiv ℂ u y).restrictScalars ℝ) y := hu.hasFDerivAt.restrictScalars ℝ
  have h4 := HasFDerivAt.const_mul (HasFDerivAt.log (ChartGram.hasFDerivAt_re_inner h1 h1)
    (ChartGram.re_inner_self_pos h0).ne') 2⁻¹
  rw [h4.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, ContinuousLinearMap.coe_restrictScalars',
    Complex.reCLM_apply, Complex.add_re, smul_eq_mul]
  rw [ChartGram.re_inner_comm (fderiv ℂ u y b)]
  ring

theorem ChartGram.hessian_half_log_apply [CompleteSpace F] {u : E → F} {y : E}
    (hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y') (h0 : u y ≠ 0) (a b : E) :
    fderiv ℝ (fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re)) y a b =
      ((⟪u y, fderiv ℂ (fderiv ℂ u) y a b⟫_ℂ).re + (⟪fderiv ℂ u y a, fderiv ℂ u y b⟫_ℂ).re) *
          ((⟪u y, u y⟫_ℂ).re)⁻¹ -
        (⟪u y, fderiv ℂ u y b⟫_ℂ).re * (2 * (⟪u y, fderiv ℂ u y a⟫_ℂ).re) *
          (((⟪u y, u y⟫_ℂ).re) ^ 2)⁻¹ := by
  set ψ : E → ℝ := fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re with hψ
  have hy : AnalyticAt ℂ u y := hu.self_of_nhds
  have hN := ChartGram.re_inner_self_pos h0

  have hc : ContDiffAt ℝ 2 ψ y := by
    have hu2 : ContDiffAt ℝ 2 u y := (hy.contDiffAt (n := 2)).restrict_scalars ℝ
    have hi : ContDiffAt ℝ 2 (fun y' => (⟪u y', u y'⟫_ℂ).re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y (ContDiffAt.inner ℂ hu2 hu2)
    exact contDiffAt_const.mul (hi.log hN.ne')
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ ψ) y a b = fderiv ℝ (fun y' => fderiv ℝ ψ y' b) y a := by
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  rw [h2]

  have hev : (fun y' => fderiv ℝ ψ y' b) =ᶠ[𝓝 y]
      fun y' => (⟪u y', fderiv ℂ u y' b⟫_ℂ).re * ((⟪u y', u y'⟫_ℂ).re)⁻¹ := by
    filter_upwards [hu, hy.continuousAt.eventually_ne h0] with y' h1 h2
    exact ChartGram.fderiv_half_log_apply h1.differentiableAt h2 b
  rw [hev.fderiv_eq]
  have hu1 : HasFDerivAt u ((fderiv ℂ u y).restrictScalars ℝ) y :=
    hy.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hW : HasFDerivAt (fun y' => fderiv ℂ u y' b)
      (((fderiv ℂ u y).comp (0 : E →L[ℂ] E) + (fderiv ℂ (fderiv ℂ u) y).flip b).restrictScalars ℝ) y :=
    (hy.fderiv.differentiableAt.hasFDerivAt.clm_apply (hasFDerivAt_const b y)).restrictScalars ℝ
  have hI := (hasDerivAt_inv hN.ne').comp_hasFDerivAt y (ChartGram.hasFDerivAt_re_inner hu1 hu1)
  have hg := HasFDerivAt.mul (ChartGram.hasFDerivAt_re_inner hu1 hW) hI
  have hg' : HasFDerivAt (fun y' => (⟪u y', fderiv ℂ u y' b⟫_ℂ).re * ((⟪u y', u y'⟫_ℂ).re)⁻¹) _ y := hg
  rw [hg'.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', Complex.reCLM_apply, Complex.add_re, smul_eq_mul,
    zero_apply, map_zero, ContinuousLinearMap.flip_apply,
    zero_add, Function.comp_apply]
  rw [ChartGram.re_inner_comm (fderiv ℂ u y a) (u y)]
  ring

open ReciprocityTheory.ChartRestriction.G.Geo (cxHessian) in

theorem ChartGram.cxHessian_half_log [CompleteSpace F] {D : ℕ} {u : (Fin D → ℂ) → F}
    {y : Fin D → ℂ} (hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y') (h0 : u y ≠ 0) (i j : Fin D) :
    cxHessian (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y i j =
      (⟪u y, u y⟫_ℂ * ⟪fderiv ℂ u y (Pi.single j 1), fderiv ℂ u y (Pi.single i 1)⟫_ℂ -
          ⟪u y, fderiv ℂ u y (Pi.single i 1)⟫_ℂ * ⟪fderiv ℂ u y (Pi.single j 1), u y⟫_ℂ) /
        (2 * ⟪u y, u y⟫_ℂ ^ 2) := by
  have hN := ChartGram.re_inner_self_pos h0
  have hNc : ⟪u y, u y⟫_ℂ = ((⟪u y, u y⟫_ℂ).re : ℂ) := by
    rw [← inner_self_ofReal_re (𝕜 := ℂ)]; rfl
  unfold cxHessian
  simp only [ChartGram.hessian_half_log_apply hu h0, map_smul, smul_apply,
    inner_smul_right, inner_smul_left, Complex.conj_I]
  rw [← inner_conj_symm (fderiv ℂ u y (Pi.single j 1)) (u y),
    ← inner_conj_symm (fderiv ℂ u y (Pi.single j 1)) (fderiv ℂ u y (Pi.single i 1)), hNc]
  generalize ⟪u y, fderiv ℂ (fderiv ℂ u) y (Pi.single i 1) (Pi.single j 1)⟫_ℂ = Q
  generalize ⟪fderiv ℂ u y (Pi.single i 1), fderiv ℂ u y (Pi.single j 1)⟫_ℂ = P
  generalize ⟪u y, fderiv ℂ u y (Pi.single i 1)⟫_ℂ = p
  generalize ⟪u y, fderiv ℂ u y (Pi.single j 1)⟫_ℂ = q
  generalize (⟪u y, u y⟫_ℂ).re = N at hN ⊢
  have hN' : N ≠ 0 := hN.ne'
  apply Complex.ext <;>
    simp [sq, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
    field_simp <;> ring

end GroundTheory.Heights₂.Heights
