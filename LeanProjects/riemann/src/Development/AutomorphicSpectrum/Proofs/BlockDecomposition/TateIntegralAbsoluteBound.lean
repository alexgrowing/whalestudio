import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealTateLocalFactor

open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C
open scoped FourierTransform

noncomputable section
namespace GlobalTheory.CompanionTheory.TateFunctionalEquationComplex

theorem integrable_chR (F : ℝ → ℂ) (e : Bool) (s : ℂ) (hm : AEStronglyMeasurable F volume)
    (h : Integrable (fun x : ℝ => F x * ((|x| ^ (s.re - 1) : ℝ) : ℂ))) :
    Integrable (fun a : ℝˣ => F a * chR e s a) mulR := by
  let g : ℝ → ℂ := fun x => F x * ((if e = true ∧ x < 0 then -1 else 1) * (((|x| : ℝ) : ℂ) ^ s))
  have hs1 : Measurable fun x : ℝ => (if e = true ∧ x < 0 then (-1 : ℂ) else 1) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    show MeasurableSet {x : ℝ | e = true ∧ x < 0}
    by_cases he : e = true
    · have hI : {x : ℝ | e = true ∧ x < 0} = Set.Iio 0 := by
        ext x
        simp [he]
      rw [hI]
      exact measurableSet_Iio
    · have hI : {x : ℝ | e = true ∧ x < 0} = ∅ := by
        ext x
        simp [he]
      rw [hI]
      exact MeasurableSet.empty
  have hs2 : Measurable fun x : ℝ => (((|x| : ℝ) : ℂ) ^ s) :=
    (Complex.measurable_ofReal.comp measurable_abs).pow_const s
  have hm' : AEStronglyMeasurable (fun x : ℝ => |x|⁻¹ • g x) volume :=
    (measurable_abs.inv).aestronglyMeasurable.smul
      (hm.mul (hs1.mul hs2).aestronglyMeasurable)
  have key : Integrable (fun x : ℝ => |x|⁻¹ • g x) volume := by
    refine h.mono hm' ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx
    have hx0 : x ≠ 0 := hx
    have hpos : 0 < |x| := abs_pos.2 hx0
    have hsg : ‖(if e = true ∧ x < 0 then (-1 : ℂ) else 1)‖ = 1 := by split_ifs <;> simp
    have hp : 0 ≤ |x| ^ (s.re - 1) := Real.rpow_nonneg hpos.le _
    have h1 : ‖|x|⁻¹ • g x‖ = ‖F x‖ * |x| ^ (s.re - 1) := by
      simp only [g]
      rw [norm_smul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, hsg,
        Real.rpow_sub_one hpos.ne', Real.norm_eq_abs, abs_inv, abs_abs]
      field_simp
    have h2 : ‖F x * ((|x| ^ (s.re - 1) : ℝ) : ℂ)‖ = ‖F x‖ * |x| ^ (s.re - 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
    rw [h1, h2]
  exact (RealTateConv.integrable_mulR_iff g).2 key

theorem fourier_scaled_swap (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    ∫ x : ℝ, g x * 𝓕 f (t * x) = ∫ x : ℝ, f x * 𝓕 g (t * x) := by
  have hL : Continuous fun p : ℝ × ℝ => (t • LinearMap.mul ℝ ℝ) p.1 p.2 := by
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    fun_prop
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (L := t • LinearMap.mul ℝ ℝ)
    (f := f) (g := g) Real.continuous_fourierChar hL hf hg
  have hF : ∀ (h : ℝ → ℂ) (y : ℝ), 𝓕 h (t * y)
      = VectorFourier.fourierIntegral Real.fourierChar volume (t • LinearMap.mul ℝ ℝ) h y := by
    intro h y
    rw [Real.fourier_real_eq, VectorFourier.fourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    congr 3
    ring
  have hF' : ∀ (h : ℝ → ℂ) (y : ℝ), 𝓕 h (t * y)
      = VectorFourier.fourierIntegral Real.fourierChar volume (t • LinearMap.mul ℝ ℝ).flip h y := by
    intro h y
    rw [Real.fourier_real_eq, VectorFourier.fourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    congr 3
    ring
  simp only [hF f, hF' g]
  simp only [smul_eq_mul] at key
  rw [← key]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem tate_zeta_symmetric (f : ℝ → ℂ) (g : SchwartzMap ℝ ℂ) (e : Bool) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hf : Integrable f) (hw : Integrable (fun w => f w * ((|w| ^ (s.re - 1) : ℝ) : ℂ)))
    (hF : Integrable (fun r => 𝓕 f r * ((|r| ^ (-s.re) : ℝ) : ℂ))) :
    z1 (𝓕 f) e (1 - s) * z1 g e s
      = z1 (SchwartzMap.fourierTransformCLM ℂ g) e (1 - s) * z1 f e s := by
  have h1' : 0 < (1 - s).re := by simpa using h1
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  have hre : (1 - s).re - 1 = -s.re := by simp
  have A : Integrable (fun a : ℝˣ => 𝓕 f a * chR e (1 - s) a) mulR :=
    integrable_chR _ e _ hcont.aestronglyMeasurable (by rw [hre]; exact hF)
  have B : Integrable (fun a : ℝˣ => f a * chR e s a) mulR :=
    integrable_chR _ e _ hf.aestronglyMeasurable hw
  have hc : ((SchwartzMap.fourierTransformCLM ℂ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) = 𝓕 (g : ℝ → ℂ) := by
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
  rw [TateR.tate_zeta_product _ _ e s A (RealTateConv.tateInt g e s h0),
    TateR.tate_zeta_product _ _ e s (RealTateConv.tateInt _ e _ h1') B, hc]
  simp only [fourier_scaled_swap f g hf g.integrable]

theorem main : TateFunctionalEquationComplex := by
  intro f e s h0 h1 hf hw hF
  have h1' : 0 < (1 - s).re := by simpa using h1
  cases e
  · obtain ⟨g, hg⟩ := TateR.gaussEven
    have key := tate_zeta_symmetric f g false s h0 h1 hf hw hF
    rw [(hg s h0).1, (hg _ h1').2] at key
    have hne := Gammaℝ_ne_zero_of_re_pos h0
    simp only [gT, Bool.false_eq_true, if_false, add_zero, one_mul]
    field_simp
    linear_combination key
  · obtain ⟨g, hg⟩ := TateR.gaussOdd
    have key := tate_zeta_symmetric f g true s h0 h1 hf hw hF
    rw [(hg s h0).1, (hg _ h1').2] at key
    have hne : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    simp only [gT, if_true]
    field_simp
    linear_combination key

end GlobalTheory.CompanionTheory.TateFunctionalEquationComplex
