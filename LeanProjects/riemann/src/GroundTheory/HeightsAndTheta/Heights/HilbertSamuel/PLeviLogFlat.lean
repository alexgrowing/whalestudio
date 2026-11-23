import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqLevi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

variable {J : Type} [Fintype J]

theorem fderiv_fderiv_add_apply {f g : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (v : J → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) z v v =
      fderiv ℝ (fderiv ℝ f) z v v + fderiv ℝ (fderiv ℝ g) z v v := by
  have hf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hg' : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z) z :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hev : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 z] fun y => fderiv ℝ f y + fderiv ℝ g y := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hy1 hy2
    exact ((hy1.differentiableAt (by norm_num)).hasFDerivAt.add
      (hy2.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have h2 : HasFDerivAt (fun y => fderiv ℝ f y + fderiv ℝ g y)
      (fderiv ℝ (fderiv ℝ f) z + fderiv ℝ (fderiv ℝ g) z) z := hf'.add hg'
  rw [hev.fderiv_eq, h2.fderiv]
  rfl

theorem fderiv_fderiv_log_apply {F : (J → ℂ) → ℝ} {z : J → ℂ} (hF : ContDiffAt ℝ 2 F z) (hpos : 0 < F z)
    (v : J → ℂ) :
    fderiv ℝ (fderiv ℝ (fun x => Real.log (F x))) z v v =
      fderiv ℝ (fderiv ℝ F) z v v / F z - (fderiv ℝ F z v) ^ 2 / F z ^ 2 := by
  have hpos' : ∀ᶠ y in 𝓝 z, 0 < F y := continuousAt_const.eventually_lt hF.continuousAt hpos
  have hev : fderiv ℝ (fun x => Real.log (F x)) =ᶠ[𝓝 z] fun y => (F y)⁻¹ • fderiv ℝ F y := by
    filter_upwards [hF.eventually (by simp), hpos'] with y hy hy'
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.log hy'.ne').fderiv
  have hH : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) z :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hinv : HasFDerivAt (fun y => (F y)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(F z ^ 2)⁻¹)).comp (fderiv ℝ F z)) z :=
    (hasFDerivAt_inv hpos.ne').comp z (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hP := hinv.fun_smul hH
  rw [hev.fderiv_eq, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  field_simp
  ring

theorem leviForm_log {F : (J → ℂ) → ℝ} {z : J → ℂ} (hF : ContDiffAt ℝ 2 F z) (hpos : 0 < F z) (w : J → ℂ) :
    leviForm (fun x => Real.log (F x)) z w =
      leviForm F z w / F z - ((fderiv ℝ F z w) ^ 2 + (fderiv ℝ F z (Complex.I • w)) ^ 2) / (4 * F z ^ 2) := by
  unfold leviForm
  rw [fderiv_fderiv_log_apply hF hpos, fderiv_fderiv_log_apply hF hpos]
  have : F z ≠ 0 := hpos.ne'
  field_simp
  ring

theorem LeviLogFlat.proof : LeviLogFlat.Statement := by
  intro J _ P u z w hP hu hpos hu0 hdw hdiw hlevi
  have hF : ContDiffAt ℝ 2 (fun x => P x + u x) z := hP.add hu
  have hFpos : 0 < P z + u z := by rw [hu0, add_zero]; exact hpos
  have hd : ∀ v, fderiv ℝ (fun x => P x + u x) z v = fderiv ℝ P z v + fderiv ℝ u z v := by
    intro v
    have h2 : HasFDerivAt (fun x => P x + u x) (fderiv ℝ P z + fderiv ℝ u z) z :=
      (hP.differentiableAt (by norm_num)).hasFDerivAt.add (hu.differentiableAt (by norm_num)).hasFDerivAt
    rw [h2.fderiv]
    rfl
  have hL : leviForm (fun x => P x + u x) z w = leviForm P z w + leviForm u z w := by
    unfold leviForm
    rw [fderiv_fderiv_add_apply hP hu, fderiv_fderiv_add_apply hP hu]
    ring
  rw [leviForm_log hF hFpos, leviForm_log hP hpos, hL, hlevi, hd, hd, hdw, hdiw, hu0]
  simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
