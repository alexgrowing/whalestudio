import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import GroundTheory.GlobalFields.TateThesis.Gaussian
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C
namespace GlobalTheory.CompanionTheory.TateR

theorem chR_mul (e : Bool) (s : ℂ) (t b : ℝˣ) :
    chR e (1 - s) (t * b) * chR e s b = chR e (1 - s) t * ((|(b : ℝ)| : ℝ) : ℂ) := by
  have hb : ((|(b : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr b.ne_zero
  have hc : (((|((t * b : ℝˣ) : ℝ)| : ℝ) : ℂ)) ^ (1 - s) * ((|(b : ℝ)| : ℝ) : ℂ) ^ s
      = ((|(t : ℝ)| : ℝ) : ℂ) ^ (1 - s) * ((|(b : ℝ)| : ℝ) : ℂ) := by
    rw [Units.val_mul, abs_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _), mul_assoc, ← cpow_add _ _ hb]
    simp
  have hsg : (if e = true ∧ ((t * b : ℝˣ) : ℝ) < 0 then (-1 : ℂ) else 1)
      * (if e = true ∧ (b : ℝ) < 0 then (-1 : ℂ) else 1)
      = (if e = true ∧ (t : ℝ) < 0 then (-1 : ℂ) else 1) := by
    cases e
    · simp
    · have hb0 := b.ne_zero
      have ht0 := t.ne_zero
      rcases lt_or_gt_of_ne hb0 with h1 | h1 <;> rcases lt_or_gt_of_ne ht0 with h2 | h2
      · simp [h1, h2, mul_pos_of_neg_of_neg h2 h1, not_lt.mpr (mul_pos_of_neg_of_neg h2 h1).le]
      · simp [h2, h1, mul_neg_of_pos_of_neg h2 h1, not_lt.mpr h2.le]
      · simp [h1, h2, mul_neg_of_neg_of_pos h2 h1, not_lt.mpr h1.le]
      · simp [h1, h2, not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr (mul_pos h2 h1).le]
  simp only [chR]
  calc _ = ((if e = true ∧ ((t * b : ℝˣ) : ℝ) < 0 then (-1 : ℂ) else 1)
      * (if e = true ∧ (b : ℝ) < 0 then (-1 : ℂ) else 1))
      * ((((|((t * b : ℝˣ) : ℝ)| : ℝ) : ℂ)) ^ (1 - s) * ((|(b : ℝ)| : ℝ) : ℂ) ^ s) := by ring
    _ = _ := by rw [hsg, hc]; ring

theorem tate_zeta_product (F G : ℝ → ℂ) (e : Bool) (s : ℂ)
    (hF : Integrable (fun a : ℝˣ => F a * chR e (1 - s) a) mulR)
    (hG : Integrable (fun a : ℝˣ => G a * chR e s a) mulR) :
    z1 F e (1 - s) * z1 G e s = ∫ t : ℝˣ, chR e (1 - s) t * (∫ x : ℝ, G x * F (t * x)) ∂mulR := by
  set A : ℝˣ → ℂ := fun a => F a * chR e (1 - s) a with hA
  set B : ℝˣ → ℂ := fun a => G a * chR e s a with hB
  have hP : Integrable (fun p : ℝˣ × ℝˣ => A p.1 * B p.2) (mulR.prod mulR) := hF.mul_prod hG
  have hT := measurePreserving_mul_prod (mulR) (mulR)
  have hP' : Integrable (fun p : ℝˣ × ℝˣ => A (p.1 * p.2) * B p.2) (mulR.prod mulR) :=
    hT.integrable_comp_of_integrable hP
  have h1 : z1 F e (1 - s) * z1 G e s = ∫ b, ∫ t, A (t * b) * B b ∂mulR ∂mulR := by
    change (∫ a, A a ∂mulR) * (∫ b, B b ∂mulR) = _
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only
    rw [integral_mul_const, integral_mul_right_eq_self A b]
  rw [h1, ← integral_integral_swap (f := fun t b => A (t * b) * B b) hP']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  have h2 : ∀ b : ℝˣ, A (t * b) * B b
      = chR e (1 - s) t * (((|(b : ℝ)| : ℝ) : ℂ) * (G b * F (t * b))) := by
    intro b
    have := chR_mul e s t b
    simp only [hA, hB, Units.val_mul]
    calc _ = F (t * b) * G b * (chR e (1 - s) (t * b) * chR e s b) := by
          ring
      _ = _ := by rw [this]; ring
  simp only [h2]
  rw [integral_const_mul]
  congr 1
  rw [integral_mulR (fun x : ℝ => ((|x| : ℝ) : ℂ) * (G x * F (t * x)))]
  refine integral_congr_ae ?_
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
  filter_upwards [h0] with x hx
  have : ((|x|⁻¹ : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (abs_ne_zero.mpr hx)]
    simp
  rw [← mul_assoc, this, one_mul]

theorem fourier_scaled_swap (f g : SchwartzMap ℝ ℂ) (t : ℝ) :
    ∫ x : ℝ, g x * (SchwartzMap.fourierTransformCLM ℂ f) (t * x)
      = ∫ x : ℝ, f x * (SchwartzMap.fourierTransformCLM ℂ g) (t * x) := by
  have hL : Continuous fun p : ℝ × ℝ => (t • LinearMap.mul ℝ ℝ) p.1 p.2 := by
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    fun_prop
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (L := t • LinearMap.mul ℝ ℝ)
    (f := (f : ℝ → ℂ)) (g := (g : ℝ → ℂ)) Real.continuous_fourierChar hL f.integrable g.integrable
  have hF : ∀ (h : SchwartzMap ℝ ℂ) (y : ℝ), (SchwartzMap.fourierTransformCLM ℂ h) (t * y)
      = VectorFourier.fourierIntegral Real.fourierChar volume (t • LinearMap.mul ℝ ℝ) (h : ℝ → ℂ) y := by
    intro h y
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, Real.fourier_real_eq,
      VectorFourier.fourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    congr 3
    ring
  have hF' : ∀ (h : SchwartzMap ℝ ℂ) (y : ℝ), (SchwartzMap.fourierTransformCLM ℂ h) (t * y)
      = VectorFourier.fourierIntegral Real.fourierChar volume (t • LinearMap.mul ℝ ℝ).flip (h : ℝ → ℂ) y := by
    intro h y
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, Real.fourier_real_eq,
      VectorFourier.fourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    congr 3
    ring
  simp only [hF f, hF' g]
  simp only [smul_eq_mul] at key
  rw [← key]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem tate_zeta_symmetric (hI : TateInt) (f g : SchwartzMap ℝ ℂ) (e : Bool) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    z1 (SchwartzMap.fourierTransformCLM ℂ f) e (1 - s) * z1 g e s
      = z1 (SchwartzMap.fourierTransformCLM ℂ g) e (1 - s) * z1 f e s := by
  have h1' : 0 < (1 - s).re := by simpa using h1
  rw [tate_zeta_product _ _ e s (hI _ e _ h1') (hI _ e _ h0), tate_zeta_product _ _ e s (hI _ e _ h1') (hI _ e _ h0)]
  simp only [fourier_scaled_swap f g]

theorem tate_integral_eq_plane_integral (F : ℝ → ℂ) (e : Bool) (s : ℂ) : z1 F e s =
    ∫ x : ℝ, ((|x|⁻¹ : ℝ) : ℂ) * (F x * ((if e = true ∧ x < 0 then (-1 : ℂ) else 1) * ((|x| : ℝ) : ℂ) ^ s)) :=
  integral_mulR (fun x : ℝ => F x * ((if e = true ∧ x < 0 then (-1 : ℂ) else 1) * ((|x| : ℝ) : ℂ) ^ s))

theorem tate_zeta_gaussian (s : ℂ) (hs : 0 < s.re) : z1 GroundTheory.Global.realGaussian false s = Gammaℝ s := by
  rw [tate_integral_eq_plane_integral, ← GroundTheory.Global.integral_realGaussian_mul_abs_cpow hs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Bool.false_eq_true, false_and, if_false, one_mul, Complex.ofReal_inv]
  rw [div_eq_mul_inv]
  ring

theorem tate_integral_odd_gaussian (s : ℂ) (hs : 0 < s.re) : z1 GroundTheory.Global.realGaussianOdd true s = Gammaℝ (s + 1) := by
  rw [tate_integral_eq_plane_integral, ← GroundTheory.Global.integral_realGaussianOdd_mul_sign_mul_abs_cpow (s := s) (by linarith)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [true_and, Complex.ofReal_inv]
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_pos h, Real.sign_of_neg h, div_eq_mul_inv]
    push_cast
    ring
  · subst h
    simp
  · rw [if_neg (not_lt.mpr h.le), Real.sign_of_pos h, div_eq_mul_inv]
    push_cast
    ring

theorem gaussS_coe : (GroundTheory.Global.gaussianSchwartz ℝ : ℝ → ℂ) = GroundTheory.Global.realGaussian := by
  funext x
  rw [GroundTheory.Global.gaussianSchwartz_apply, GroundTheory.Global.realGaussian_eq_ofReal]
  simp

theorem gaussEven : ∃ g : SchwartzMap ℝ ℂ, ∀ s : ℂ, 0 < s.re →
    z1 g false s = Gammaℝ s ∧ z1 (SchwartzMap.fourierTransformCLM ℂ g) false s = Gammaℝ s := by
  refine ⟨GroundTheory.Global.gaussianSchwartz ℝ, fun s hs => ?_⟩
  have h : ((SchwartzMap.fourierTransformCLM ℂ (GroundTheory.Global.gaussianSchwartz ℝ) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = GroundTheory.Global.realGaussian := by
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, gaussS_coe,
      GroundTheory.Global.fourier_realGaussian]
  rw [h, gaussS_coe]
  exact ⟨tate_zeta_gaussian s hs, tate_zeta_gaussian s hs⟩

theorem gaussOdd : ∃ g : SchwartzMap ℝ ℂ, ∀ s : ℂ, 0 < s.re →
    z1 g true s = Gammaℝ (s + 1) ∧
      z1 (SchwartzMap.fourierTransformCLM ℂ g) true s = -I * Gammaℝ (s + 1) := by
  set g₁ : SchwartzMap ℝ ℂ :=
    (-(1 / (2 * Real.pi)) : ℂ) • SchwartzMap.derivCLM ℂ ℂ (GroundTheory.Global.gaussianSchwartz ℝ) with hg₁
  have hc : (g₁ : ℝ → ℂ) = GroundTheory.Global.realGaussianOdd := by
    funext x
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [hg₁, SchwartzMap.smul_apply, SchwartzMap.derivCLM_apply, gaussS_coe,
      (GroundTheory.Global.hasDerivAt_realGaussian x).deriv, GroundTheory.Global.realGaussianOdd,
      ← GroundTheory.Global.realGaussian, smul_eq_mul]
    field_simp
  have hf : ((SchwartzMap.fourierTransformCLM ℂ g₁ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun y => -I * GroundTheory.Global.realGaussianOdd y := by
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, hc,
      GroundTheory.Global.fourier_realGaussianOdd]
  refine ⟨g₁, fun s hs => ?_⟩
  rw [hf, hc]
  refine ⟨tate_integral_odd_gaussian s hs, ?_⟩
  rw [← tate_integral_odd_gaussian s hs]
  simp only [z1, mul_assoc]
  rw [integral_const_mul]

theorem tateR_of_int (hI : TateInt) : TateR := by
  intro f e s h0 h1
  have h1' : 0 < (1 - s).re := by simpa using h1
  cases e
  · obtain ⟨g, hg⟩ := gaussEven
    have key := tate_zeta_symmetric hI f g false s h0 h1
    rw [(hg s h0).1, (hg _ h1').2] at key
    have hne := Gammaℝ_ne_zero_of_re_pos h0
    simp only [gT, Bool.false_eq_true, if_false, add_zero, one_mul]
    field_simp
    linear_combination key
  · obtain ⟨g, hg⟩ := gaussOdd
    have key := tate_zeta_symmetric hI f g true s h0 h1
    rw [(hg s h0).1, (hg _ h1').2] at key
    have hne : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    simp only [gT, if_true]
    field_simp
    linear_combination key

theorem tateR : TateR := tateR_of_int GlobalTheory.T.archimedean_tate_integral

end GlobalTheory.CompanionTheory.TateR
