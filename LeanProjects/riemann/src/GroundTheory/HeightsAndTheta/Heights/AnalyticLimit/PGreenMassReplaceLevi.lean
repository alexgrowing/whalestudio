import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)

noncomputable section

variable {ι : Type} [Fintype ι]

theorem fderiv2_comp_real {ψ : (ι → ℂ) → ℝ} {G G₁ : ℝ → ℝ} {g₂ : ℝ} {y : ι → ℂ}
    (hψ : ContDiffAt ℝ 2 ψ y) (hG : ∀ᶠ z in 𝓝 y, HasDerivAt G (G₁ (ψ z)) (ψ z))
    (hG₁ : HasDerivAt G₁ g₂ (ψ y)) (v w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => G (ψ z))) y v w =
      G₁ (ψ y) * fderiv ℝ (fderiv ℝ ψ) y v w + g₂ * fderiv ℝ ψ y v * fderiv ℝ ψ y w := by
  have hev : fderiv ℝ (fun z => G (ψ z)) =ᶠ[𝓝 y] fun z => G₁ (ψ z) • fderiv ℝ ψ z := by
    filter_upwards [hG, hψ.eventually (by simp)] with z h1 h2
    exact (h1.comp_hasFDerivAt z (h2.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hD2 : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) y) y :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (fun z => G₁ (ψ z)) (g₂ • fderiv ℝ ψ y) y :=
    hG₁.comp_hasFDerivAt y (hψ.differentiableAt (by norm_num)).hasFDerivAt
  have h := ((hc.smul hD2).congr_of_eventuallyEq hev).fderiv
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]

theorem fderiv_comp_real {ψ : (ι → ℂ) → ℝ} {G : ℝ → ℝ} {g₁ : ℝ} {y : ι → ℂ}
    (hψ : DifferentiableAt ℝ ψ y) (hG : HasDerivAt G g₁ (ψ y)) (v : ι → ℂ) :
    fderiv ℝ (fun z => G (ψ z)) y v = g₁ * fderiv ℝ ψ y v := by
  have h := (hG.comp_hasFDerivAt y hψ.hasFDerivAt).fderiv
  rw [show (fun z => G (ψ z)) = G ∘ ψ from rfl, h]
  simp

theorem levi_comp_real {ψ : (ι → ℂ) → ℝ} {G G₁ : ℝ → ℝ} {g₂ : ℝ} {y : ι → ℂ}
    (hψ : ContDiffAt ℝ 2 ψ y) (hG : ∀ᶠ z in 𝓝 y, HasDerivAt G (G₁ (ψ z)) (ψ z))
    (hG₁ : HasDerivAt G₁ g₂ (ψ y)) (w : ι → ℂ) :
    levi (fun z => G (ψ z)) y w = G₁ (ψ y) * levi ψ y w +
      g₂ * ((fderiv ℝ ψ y w) ^ 2 + (fderiv ℝ ψ y (Complex.I • w)) ^ 2) / 4 := by
  unfold levi
  rw [fderiv2_comp_real hψ hG hG₁, fderiv2_comp_real hψ hG hG₁]
  ring

theorem fderiv_re_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => (S z).re) y v = (fderiv ℂ S y v).re := by
  have hS' : HasFDerivAt S ((fderiv ℂ S y).restrictScalars ℝ) y :=
    hS.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have h := (Complex.reCLM.hasFDerivAt.comp y hS').fderiv
  rw [show (fun z => (S z).re) = Complex.reCLM ∘ S from rfl, h]
  simp

theorem im_eq_re_mul (c : ℂ) : c.im = (-Complex.I * c).re := by
  simp [Complex.mul_re]

theorem fderiv_im_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => (S z).im) y v = (fderiv ℂ S y v).im := by
  have hS2 : AnalyticAt ℂ (fun z => -Complex.I * S z) y := analyticAt_const.mul hS
  have h1 : (fun z => (S z).im) = fun z => (-Complex.I * S z).re := funext fun z => im_eq_re_mul _
  rw [h1, fderiv_re_analytic hS2, fderiv_const_mul hS.differentiableAt]
  simp [Complex.mul_re]

theorem levi_im_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (w : ι → ℂ) :
    levi (fun z => (S z).im) y w = 0 := by
  have hS2 : AnalyticAt ℂ (fun z => -Complex.I * S z) y := analyticAt_const.mul hS
  have h1 : (fun z => (S z).im) = fun z => (-Complex.I * S z).re := funext fun z => im_eq_re_mul _
  rw [h1]
  exact levi_re_analytic hS2 w

theorem contDiffAt_re_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) :
    ContDiffAt ℝ 2 (fun z => (S z).re) y :=
  (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y (hS.restrictScalars (𝕜 := ℝ)).contDiffAt

theorem contDiffAt_im_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) :
    ContDiffAt ℝ 2 (fun z => (S z).im) y :=
  (Complex.imCLM.contDiff (n := 2)).contDiffAt.comp y (hS.restrictScalars (𝕜 := ℝ)).contDiffAt

theorem sq_norm_eq_re_im (c : ℂ) : ‖c‖ ^ 2 = c.re ^ 2 + 1 * c.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem hasDerivAt_sq' (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

theorem levi_normSq_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (w : ι → ℂ) :
    levi (fun z => ‖S z‖ ^ 2) y w = ‖fderiv ℂ S y w‖ ^ 2 := by
  have hre := contDiffAt_re_analytic hS
  have him := contDiffAt_im_analytic hS
  have e : (fun z => ‖S z‖ ^ 2) = fun z => (S z).re ^ 2 + 1 * (S z).im ^ 2 :=
    funext fun z => sq_norm_eq_re_im _
  have hG : ∀ (ψ : (ι → ℂ) → ℝ), ∀ᶠ z in 𝓝 y, HasDerivAt (fun x : ℝ => x ^ 2) (2 * ψ z) (ψ z) :=
    fun ψ => Eventually.of_forall fun z => hasDerivAt_sq' _
  have hG₁ : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 2 * x) 2 x := fun x => by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have l1 := levi_comp_real (G₁ := fun x => 2 * x) hre (hG _) (hG₁ _) w
  have l2 := levi_comp_real (G₁ := fun x => 2 * x) him (hG _) (hG₁ _) w
  have hsq : ∀ (ψ : (ι → ℂ) → ℝ), ContDiffAt ℝ 2 ψ y → ContDiffAt ℝ 2 (fun z => ψ z ^ 2) y :=
    fun ψ h => h.pow 2
  rw [e, levi_add_smul 1 (hsq _ hre) (hsq _ him), l1, l2, levi_re_analytic hS,
    levi_im_analytic hS, fderiv_re_analytic hS, fderiv_re_analytic hS, fderiv_im_analytic hS,
    fderiv_im_analytic hS, map_smul, sq_norm_eq_re_im]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

theorem fderiv_normSq_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => ‖S z‖ ^ 2) y v =
      2 * ((S y).re * (fderiv ℂ S y v).re + (S y).im * (fderiv ℂ S y v).im) := by
  have hre := contDiffAt_re_analytic hS
  have him := contDiffAt_im_analytic hS
  have e : (fun z => ‖S z‖ ^ 2) = fun z => (S z).re ^ 2 + (S z).im ^ 2 :=
    funext fun z => by rw [sq_norm_eq_re_im, one_mul]
  have d1 : DifferentiableAt ℝ (fun z => (S z).re ^ 2) y :=
    (hre.differentiableAt (by norm_num)).pow 2
  have d2 : DifferentiableAt ℝ (fun z => (S z).im ^ 2) y :=
    (him.differentiableAt (by norm_num)).pow 2
  rw [e, fderiv_fun_add d1 d2, ContinuousLinearMap.add_apply,
    fderiv_comp_real (G := fun x : ℝ => x ^ 2) (hre.differentiableAt (by norm_num))
      (hasDerivAt_sq' _),
    fderiv_comp_real (G := fun x : ℝ => x ^ 2) (him.differentiableAt (by norm_num))
      (hasDerivAt_sq' _), fderiv_re_analytic hS, fderiv_im_analytic hS]
  ring

theorem levi_log_normSq_add_exp {S : (ι → ℂ) → ℂ} {Φ : (ι → ℂ) → ℝ} {y : ι → ℂ} {ε : ℝ}
    (hS : AnalyticAt ℂ S y) (hΦ : ContDiffAt ℝ 2 Φ y) (hε : 0 < ε) (w : ι → ℂ) :
    2 * (ε * Real.exp (2 * Φ y)) / (‖S y‖ ^ 2 + ε * Real.exp (2 * Φ y)) * levi Φ y w ≤
      levi (fun z => Real.log (‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z))) y w := by
  set h : (ι → ℂ) → ℝ := fun z => ‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z) with hh
  have hpos : ∀ z, 0 < h z := fun z => by
    have := Real.exp_pos (2 * Φ z)
    positivity
  have hSc : ContDiffAt ℝ 2 S y := (hS.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hQ : ContDiffAt ℝ 2 (fun z => ‖S z‖ ^ 2) y := (contDiff_norm_sq ℝ).contDiffAt.comp y hSc
  have h2Φ : ContDiffAt ℝ 2 (fun z => 2 * Φ z) y := contDiffAt_const.mul hΦ
  have hE : ContDiffAt ℝ 2 (fun z => Real.exp (2 * Φ z)) y := h2Φ.exp
  have hhc : ContDiffAt ℝ 2 h y := hQ.add (contDiffAt_const.mul hE)
  have l2Φ := levi_comp_real (G := fun x : ℝ => 2 * x) (G₁ := fun _ => 2) (g₂ := 0) hΦ
    (Eventually.of_forall fun z => by simpa using (hasDerivAt_id (Φ z)).const_mul (2 : ℝ))
    (hasDerivAt_const _ _) w
  have lE := levi_comp_real (G := Real.exp) (G₁ := Real.exp) (g₂ := Real.exp (2 * Φ y)) h2Φ
    (Eventually.of_forall fun z => Real.hasDerivAt_exp _) (Real.hasDerivAt_exp _) w
  have d2Φ : ∀ v, fderiv ℝ (fun z => 2 * Φ z) y v = 2 * fderiv ℝ Φ y v := fun v =>
    fderiv_comp_real (G := fun x : ℝ => 2 * x) (hΦ.differentiableAt (by norm_num))
      (by simpa using (hasDerivAt_id (Φ y)).const_mul (2 : ℝ)) v
  have dE : ∀ v, fderiv ℝ (fun z => Real.exp (2 * Φ z)) y v =
      Real.exp (2 * Φ y) * (2 * fderiv ℝ Φ y v) := fun v => by
    rw [fderiv_comp_real (G := Real.exp) (h2Φ.differentiableAt (by norm_num))
      (Real.hasDerivAt_exp _), d2Φ]
  have dh : ∀ v, fderiv ℝ h y v = 2 * ((S y).re * (fderiv ℂ S y v).re +
      (S y).im * (fderiv ℂ S y v).im) + ε * (Real.exp (2 * Φ y) * (2 * fderiv ℝ Φ y v)) := by
    intro v
    have d1 : DifferentiableAt ℝ (fun z => ‖S z‖ ^ 2) y := hQ.differentiableAt (by norm_num)
    have d2 : DifferentiableAt ℝ (fun z => ε * Real.exp (2 * Φ z)) y :=
      (contDiffAt_const.mul hE).differentiableAt (by norm_num)
    rw [hh, fderiv_fun_add d1 d2, ContinuousLinearMap.add_apply, fderiv_normSq_analytic hS,
      fderiv_const_mul (hE.differentiableAt (by norm_num)), ContinuousLinearMap.smul_apply,
      dE, smul_eq_mul]
  have lh : levi h y w = ‖fderiv ℂ S y w‖ ^ 2 + ε * (Real.exp (2 * Φ y) * (2 * levi Φ y w) +
      Real.exp (2 * Φ y) * ((2 * fderiv ℝ Φ y w) ^ 2 +
        (2 * fderiv ℝ Φ y (Complex.I • w)) ^ 2) / 4) := by
    rw [hh, levi_add_smul ε hQ hE, levi_normSq_analytic hS, lE, l2Φ, d2Φ, d2Φ]
    ring
  have lK := levi_comp_real (G := Real.log) (G₁ := fun x => x⁻¹) (g₂ := -(h y ^ 2)⁻¹) hhc
    (Eventually.of_forall fun z => Real.hasDerivAt_log (hpos z).ne')
    (hasDerivAt_inv (hpos y).ne') w
  change _ ≤ levi (fun z => Real.log (h z)) y w
  rw [lK, lh, dh, dh, (fderiv ℂ S y).map_smul Complex.I w, sq_norm_eq_re_im (fderiv ℂ S y w)]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  set E := ε * Real.exp (2 * Φ y) with hEdef
  have hEpos : 0 < E := mul_pos hε (Real.exp_pos _)
  have hy : h y = ‖S y‖ ^ 2 + E := rfl
  rw [sq_norm_eq_re_im (S y)] at hy
  set σr := (S y).re
  set σi := (S y).im
  set ar := (fderiv ℂ S y w).re
  set ai := (fderiv ℂ S y w).im
  set b₁ := fderiv ℝ Φ y w
  set b₂ := fderiv ℝ Φ y (Complex.I • w)
  set L := levi Φ y w
  have hhy : 0 < h y := hpos y
  rw [show ‖S y‖ ^ 2 + E = h y from rfl]
  have key : (h y)⁻¹ * (ar ^ 2 + 1 * ai ^ 2 + ε * (Real.exp (2 * Φ y) * (2 * L) +
      Real.exp (2 * Φ y) * ((2 * b₁) ^ 2 + (2 * b₂) ^ 2) / 4)) +
      -(h y ^ 2)⁻¹ * ((2 * (σr * ar + σi * ai) + ε * (Real.exp (2 * Φ y) * (2 * b₁))) ^ 2 +
        (2 * (σr * (0 * ar - 1 * ai) + σi * (0 * ai + 1 * ar)) +
          ε * (Real.exp (2 * Φ y) * (2 * b₂))) ^ 2) / 4 - 2 * E / h y * L =
      E * ((ar - (σr * b₁ + σi * b₂)) ^ 2 + (ai - (σi * b₁ - σr * b₂)) ^ 2) / h y ^ 2 := by
    rw [hy]
    field_simp
    rw [hEdef]
    ring
  have hnn : 0 ≤ E * ((ar - (σr * b₁ + σi * b₂)) ^ 2 + (ai - (σi * b₁ - σr * b₂)) ^ 2) / h y ^ 2 :=
    by positivity
  linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
