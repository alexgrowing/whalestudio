import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.resCob :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H) (k : H), F.Cob (k - F.av wR k) ∧
      ∫ t in Iic (0 : ℝ), Real.exp t * ‖F.U t k - k‖ ^ 2 = 2 * ‖k‖ ^ 2 - 2 * (⟪k, F.av wR k⟫_ℂ).re := by
  intro H _ _ _ F k
  have hw := (avSpec F).2.1
  have sp := fun h => ((avSpec F).2.2.2 _ hw).1 h
  have cg : Continuous fun r : ℝ => (Real.exp r : ℂ) • F.U r k := by
    have := F.cont k
    fun_prop
  have ig : ∀ t, IntegrableOn (fun r : ℝ => (Real.exp r : ℂ) • F.U r k) (Iic t) := fun t =>
    Integrable.mono' ((integrableOn_exp_Iic t).mul_const ‖k‖) cg.aestronglyMeasurable
      (Eventually.of_forall fun r => by simp [norm_smul, F.norm])
  have R0 : ∀ h, F.av wR h = ∫ r in Iic (0 : ℝ), (Real.exp r : ℂ) • F.U r h := fun h => by
    rw [(sp h).2, ← integral_indicator measurableSet_Iic]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Iic (0 : ℝ) <;> simp [wR, hr]
  constructor
  · set c := F.av wR k with hc
    have Ut : ∀ t, F.U t c = (Real.exp (-t) : ℂ) • (c + ∫ r in (0 : ℝ)..t, (Real.exp r : ℂ) • F.U r k) := fun t => by
      rw [hc, R0, ← intervalIntegral.integral_Iic_sub_Iic (ig 0) (ig t), add_sub_cancel,
        ← (F.U t).integral_comp_comm (ig 0), ← integral_smul, ← integral_indicator measurableSet_Iic,
        ← integral_indicator measurableSet_Iic, ← integral_add_right_eq_self _ (-t)]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      by_cases hr : r ≤ t
      · simp only [indicator_of_mem (show r + -t ∈ Iic (0 : ℝ) by simpa using hr), indicator_of_mem (show r ∈ Iic t from hr),
          map_smul, ← F.add, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
        congr 3 <;> ring
      · simp only [indicator_of_notMem (show r + -t ∉ Iic (0 : ℝ) by simpa using hr), indicator_of_notMem (show r ∉ Iic t from hr)]
    have der : ∀ t, HasDerivAt (fun t => F.U t c) (F.U t (k - c)) t := fun t => by
      have d1 : HasDerivAt (fun t : ℝ => (Real.exp (-t) : ℂ)) (-(Real.exp (-t) : ℂ)) t := by
        simpa using ((hasDerivAt_neg t).exp).ofReal_comp
      have d2 := (cg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add c
      have d3 := d1.smul d2
      refine (d3.congr_of_eventuallyEq (Eventually.of_forall Ut)).congr_deriv ?_
      symm
      rw [map_sub, Ut, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one,
        one_smul, neg_smul, sub_eq_add_neg]
    refine ⟨c, fun t => ?_⟩
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => der s) ((F.cont _).intervalIntegrable _ _), F.zero]
  · have i1 : IntegrableOn (fun r : ℝ => ⟪k, (Real.exp r : ℂ) • F.U r k⟫_ℂ) (Iic 0) := (ig 0).const_inner k
    rw [R0, ← integral_inner (ig 0), ← RCLike.re_to_complex, ← integral_re i1, ← integral_const_mul]
    have e : 2 * ‖k‖ ^ 2 = ∫ t in Iic (0 : ℝ), Real.exp t * (2 * ‖k‖ ^ 2) := by
      rw [integral_mul_const, integral_exp_Iic_zero, one_mul]
    rw [e, ← integral_sub ((integrableOn_exp_Iic 0).mul_const _) (i1.re.const_mul 2)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [norm_sub_rev (F.U t k) k, @norm_sub_sq ℂ, F.norm, inner_smul_right, RCLike.re_to_complex, Complex.re_ofReal_mul]
    ring
