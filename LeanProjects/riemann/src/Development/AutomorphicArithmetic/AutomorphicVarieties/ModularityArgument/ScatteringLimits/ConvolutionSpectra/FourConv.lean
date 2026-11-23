import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.FourAe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.fourConv :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → ∀ u : L V, ∀ᵐ ξ : ℝ,
      Lp.fourierTransformₗᵢ ℝ W (conv κ u) ξ = symb κ (2 * Real.pi * Complex.I * ξ) (Lp.fourierTransformₗᵢ ℝ V u ξ) := by
  intro V _ _ _ _ W _ _ _ _ κ hk u
  have ki : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
  let σ : ℝ → V →L[ℂ] W := fun ξ => symb κ (2 * Real.pi * Complex.I * ξ)
  have hσ : ∀ ξ, σ ξ = 𝓕 (fun t => κ (-t)) ξ := fun ξ => by
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [neg_neg]
    congr 2
    push_cast; ring
  have σc : Continuous σ := by
    rw [show σ = _ from funext hσ]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ ki.comp_neg
  have σb : ∀ ξ, ‖σ ξ‖ ≤ ∫ t, ‖κ (-t)‖ := fun ξ => by
    rw [hσ]; exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  set C := ∫ t, ‖κ (-t)‖
  have hm : ∀ v : L V, MemLp (fun ξ => σ ξ (v ξ)) 2 volume := fun v =>
    (Lp.memLp v).of_le_mul (c := C)
      ((ContinuousLinearMap.id ℂ (V →L[ℂ] W)).aestronglyMeasurable_comp₂ σc.aestronglyMeasurable (Lp.aestronglyMeasurable v))
      (Eventually.of_forall fun ξ => (σ ξ).le_of_opNorm_le (σb ξ) _)
  let T : L V → L W := fun v => (hm v).toLp _
  have Tc : Continuous T := by
    refine (LipschitzWith.of_dist_le' (K := C) fun v v' => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm]
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub (T v) (T v'), Lp.coeFn_sub v v', (hm v).coeFn_toLp, (hm v').coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, ← map_sub]
    exact (σ x).le_of_opNorm_le (σb x) _
  have key : Lp.fourierTransformₗᵢ ℝ W (conv κ u) = T (Lp.fourierTransformₗᵢ ℝ V u) := by
    refine DenseRange.induction_on (p := fun u : L V => Lp.fourierTransformₗᵢ ℝ W (conv κ u) = T (Lp.fourierTransformₗᵢ ℝ V u))
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := V) (p := 2) (μ := volume) ENNReal.ofNat_ne_top) u
      (isClosed_eq ((Lp.fourierTransformₗᵢ ℝ W).continuous.comp (conv κ).continuous)
        (Tc.comp (Lp.fourierTransformₗᵢ ℝ V).continuous)) fun f => ?_
    set w : L V := SchwartzMap.toLpCLM ℝ V 2 volume f
    have wi : Integrable (w : ℝ → V) := f.integrable.congr (f.coeFn_toLp 2 volume).symm
    have e : (conv κ w : ℝ → W) =ᵐ[volume] convolution (fun t => κ (-t)) w (ContinuousLinearMap.id ℂ (V →L[ℂ] W)) volume := by
      filter_upwards [(convSpec κ hk w).1] with x hx
      rw [hx, convolution_def, ← integral_neg_eq_self]
      simp [sub_eq_add_neg]
    have ci : Integrable (conv κ w : ℝ → W) := (ki.comp_neg.integrable_convolution _ wi).congr e.symm
    refine Lp.ext ?_
    filter_upwards [fourAe _ ci, fourAe _ wi, (hm (Lp.fourierTransformₗᵢ ℝ V w)).coeFn_toLp] with ξ h1 h2 h3
    rw [h1, h3, h2, Real.fourier_congr_ae e, Real.fourier_bilin_convolution_eq _ ki.comp_neg wi, hσ]
    rfl
  rw [key]
  exact (hm _).coeFn_toLp
