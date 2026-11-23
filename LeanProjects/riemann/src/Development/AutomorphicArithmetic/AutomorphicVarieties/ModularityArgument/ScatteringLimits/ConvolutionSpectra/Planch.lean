import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.FourAe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.KvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem r_int : Integrable (fun y : ℝ => ((1 + |y|) ^ 2)⁻¹) ∧ ∫ y : ℝ, ((1 + |y|) ^ 2)⁻¹ = 2 := by
  constructor
  · refine integrable_inv_one_add_sq.mono' (Continuous.aestronglyMeasurable (Continuous.inv₀ (by fun_prop) fun y => by positivity))
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    refine inv_anti₀ (by positivity) ?_
    nlinarith [abs_nonneg y, sq_abs y]
  · rw [integral_comp_abs (f := fun y => ((1 + y) ^ 2)⁻¹)]
    have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (g := fun y : ℝ => -(1 + y)⁻¹) (g' := fun y => ((1 + y) ^ 2)⁻¹) (l := 0)
      (fun y hy => by
        have h0 : (1 + y) ≠ 0 := by have : 0 ≤ y := hy; positivity
        have := (((hasDerivAt_id y).const_add 1).inv h0).neg
        exact this.congr_deriv (by simp only [id]; rw [neg_div, neg_neg, one_div]))
      (fun y _ => by positivity)
      (by simpa using (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ (1 : ℝ) tendsto_id)).neg)
    rw [h]; norm_num

private theorem symb_app {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W) (hk : Ker κ) (z : ℂ) (e : V) :
    symb κ z e = ∫ t : ℝ, Complex.exp (z * t) • κ t e := by
  have c1 : Continuous fun t : ℝ => Complex.exp (z * t) • κ t :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul hk.1
  have s1 : HasCompactSupport fun t : ℝ => Complex.exp (z * t) • κ t := hk.2.mono fun t ht h => ht (by simp [h])
  exact ContinuousLinearMap.integral_apply (c1.integrable_of_hasCompactSupport s1) e

theorem UpperTheory.V.Z.IntegralApplyAeEq.planch :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W) (K : ℝ), Ker κ → (∀ y : ℝ, ‖symb κ (1 + y * Complex.I)‖ ≤ K / (1 + |y|)) →
      ∀ e, WLe (-2) (kv κ e) (K / √3 * ‖e‖) := by
  intro V _ _ _ _ W _ _ _ _ κ K hk hb e
  let f : ℝ → W := fun t => (Real.exp t : ℂ) • κ t e
  have fc : Continuous f := (Complex.continuous_ofReal.comp Real.continuous_exp).smul (hk.1.clm_apply continuous_const)
  have fs : HasCompactSupport f := hk.2.mono fun t ht h => ht (by simp [f, h])
  have fm : MemLp f 2 volume := fc.memLp_of_hasCompactSupport fs
  have fi : Integrable f := fc.integrable_of_hasCompactSupport fs
  have e1 : ∀ᵐ x : ℝ, ‖f (-x)‖ ^ 2 = Real.exp (-2 * x) * ‖kv κ e x‖ ^ 2 := by
    filter_upwards [((kvSpec κ hk).1 e).1] with x hx
    rw [hx, norm_smul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have i2 : Integrable fun x => ‖f x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm fc.aestronglyMeasurable).1 fm
  refine ⟨i2.comp_neg.congr e1, ?_⟩
  rw [← integral_congr_ae e1, integral_neg_eq_self fun x => ‖f x‖ ^ 2]
  have nn : ∀ u : L W, ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := fun u => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner u u)]
    simp only [inner_self_eq_norm_sq]
  have e2 : ∫ x, ‖f x‖ ^ 2 = ‖Lp.fourierTransformₗᵢ ℝ W (fm.toLp f)‖ ^ 2 := by
    rw [LinearIsometryEquiv.norm_map, nn]
    exact integral_congr_ae (fm.coeFn_toLp.mono fun x hx => by simp only [hx])
  have hF : ∀ ξ : ℝ, 𝓕 f ξ = symb κ (1 + ((-(2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I) e := fun ξ => by
    rw [Real.fourier_real_eq_integral_exp_smul, symb_app κ hk]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [f, smul_smul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2; push_cast; ring
  obtain ⟨ri, rv⟩ := r_int
  rw [e2, nn]
  calc _ ≤ ∫ ξ, (K * ‖e‖) ^ 2 * ((1 + |2 * Real.pi * ξ|) ^ 2)⁻¹ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          ((ri.comp_mul_left' (R := 2 * Real.pi) (by positivity)).const_mul _) ?_
        filter_upwards [fourAe (fm.toLp f) (fi.congr fm.coeFn_toLp.symm)] with ξ hξ
        rw [hξ, Real.fourier_congr_ae fm.coeFn_toLp, hF]
        have h1 := (symb κ _).le_of_opNorm_le (hb (-(2 * Real.pi * ξ))) e
        rw [abs_neg] at h1
        refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans_eq ?_
        field_simp
    _ = (K * ‖e‖) ^ 2 * (|(2 * Real.pi)⁻¹| * 2) := by
        rw [integral_const_mul, Measure.integral_comp_mul_left (fun y : ℝ => ((1 + |y|) ^ 2)⁻¹), smul_eq_mul, rv]
    _ ≤ _ := by
        rw [div_mul_eq_mul_div, div_pow, Real.sq_sqrt (by norm_num), div_eq_mul_inv, abs_of_pos (by positivity)]
        gcongr
        rw [mul_inv, mul_right_comm, inv_mul_cancel₀ two_ne_zero, one_mul]
        exact inv_anti₀ (by norm_num) Real.pi_gt_three.le
