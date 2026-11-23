import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

open MeasureTheory in
theorem UpperTheory.ConvolutionTheory.G.quotFub_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotFub := by
  intro _ hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP X _ m _ F hF hinv ρ hρ hfin
  haveI : μ.IsHaarMeasure := hP.1.1
  have hρm : Measurable (fun x => ((ρ x).toReal : ℂ)) :=
    Complex.measurable_ofReal.comp hρ.1.ennreal_toReal
  have hH : Measurable (Function.uncurry fun (a : X) (x : G) => F a x * ((ρ x).toReal : ℂ)) :=
    hF.mul (hρm.comp measurable_snd)
  have hint : Integrable (Function.uncurry fun (a : X) (x : G) => F a x * ((ρ x).toReal : ℂ)) (m.prod μ) := by
    refine ⟨hH.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ hH.enorm.aemeasurable]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hfin)
    refine lintegral_mono fun a => lintegral_mono fun x => ?_
    simp only [Function.uncurry, enorm_mul]
    gcongr
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  have hGm : Measurable (fun g => ∫ a, F a g ∂m) :=
    (hF.stronglyMeasurable.integral_prod_left).measurable
  have hGi : ∀ t g, (fun g => ∫ a, F a g ∂m) (j t * g) = (fun g => ∫ a, F a g ∂m) g := by
    intro t g
    simp only [hinv]
  obtain ⟨h1, -, h3⟩ := hE G T μ j ν hP _ hGm hGi ρ hρ
  have hmul : ∀ x, (∫ a, F a x ∂m) * ((ρ x).toReal : ℂ) = ∫ a, F a x * ((ρ x).toReal : ℂ) ∂m :=
    fun x => (integral_mul_const _ _).symm
  refine ⟨h1.2 ?_, ?_⟩
  · simp only [hmul]
    exact hint.integral_prod_right
  · rw [h3]
    simp only [hmul]
    rw [← integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    exact ((hE G T μ j ν hP (F a) (hF.of_uncurry_left) (hinv a) ρ hρ).2.2).symm
