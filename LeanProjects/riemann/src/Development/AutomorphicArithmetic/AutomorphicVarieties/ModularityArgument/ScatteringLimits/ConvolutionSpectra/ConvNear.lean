import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem ker_bd {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {κ : ℝ → V →L[ℂ] W} (h : HasCompactSupport κ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R < |t| → κ t = 0 := by
  obtain ⟨R, hR⟩ := h.isCompact.isBounded.exists_norm_le
  refine ⟨|R|, abs_nonneg _, fun t ht => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
  exact absurd ((hR t hm).trans (le_abs_self R)) (not_le.2 ht)

theorem UpperTheory.V.Z.IntegralApplyAeEq.convNear :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (β : ℝ → V →L[ℂ] V), Ker β → ∃ C : ℝ, ∀ u : L V,
      ‖conv β u - (symb β 0).compLpL 2 volume u‖ ^ 2 ≤ C * ∫ t in Iic (0 : ℝ), Real.exp t * ‖sh V t u - u‖ ^ 2 := by
  intro V _ _ _ _ β hk
  obtain ⟨R, hR0, hR⟩ := ker_bd hk.2
  have hk1 : Integrable β := hk.1.integrable_of_hasCompactSupport hk.2
  obtain ⟨B, hB⟩ := hk.1.bounded_above_of_compact_support hk.2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let c : (V →L[ℂ] V) →L[ℂ] (L V →L[ℂ] L V) := LinearMap.mkContinuous
    { toFun := fun A => A.compLpL 2 volume
      map_add' := fun A B => ContinuousLinearMap.add_compLpL A B
      map_smul' := fun a A => ContinuousLinearMap.smul_compLpL a A } 1 fun A => by
      rw [one_mul]; exact ContinuousLinearMap.norm_compLpL_le A
  refine ⟨(2 * B) ^ 2 * (R * Real.exp R), fun u => ?_⟩
  set d : ℝ → ℝ := fun t => ‖sh V t u - u‖ with hd
  have dc : Continuous d := (((shF V).cont u).sub continuous_const).norm
  have dn : ∀ t, d (-t) = d t := fun t => by
    show ‖(shF V).U (-t) u - u‖ = ‖(shF V).U t u - u‖
    rw [← (shF V).norm t, map_sub, ← (shF V).add, add_neg_cancel, (shF V).zero, norm_sub_rev]
  have d2 : ∀ t, d t ≤ 2 * ‖u‖ := fun t => (norm_sub_le _ _).trans_eq (by
    rw [show ‖sh V t u‖ = ‖u‖ from (shF V).norm t u]; ring)
  have i2 : Integrable fun t => c (β t) u := (c.integrable_comp hk1).apply_continuousLinearMap u
  have e1 : (symb β 0).compLpL 2 volume u = ∫ t, c (β t) u := by
    rw [symb]
    simp only [zero_mul, Complex.exp_zero, one_smul]
    rw [← ContinuousLinearMap.integral_apply (c.integrable_comp hk1), c.integral_comp_comm hk1]
    rfl
  have e2 : ‖conv β u - (symb β 0).compLpL 2 volume u‖ ≤ 2 * B * ∫ t in (-R)..0, d t := by
    rw [(convSpec β hk u).2.2, e1, ← integral_sub (convSpec β hk u).2.1 i2]
    have hb : Integrable ((Icc (-R) R).indicator fun t => B * d t) :=
      (integrable_indicator_iff measurableSet_Icc).2 ((dc.const_mul B).integrableOn_Icc)
    refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun t => ?_)).trans_eq ?_
    · by_cases h : t ∈ Icc (-R) R
      · rw [indicator_of_mem h]
        show ‖c (β t) (sh V t u) - c (β t) u‖ ≤ _
        rw [← map_sub]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        gcongr
        exact (ContinuousLinearMap.norm_compLpL_le _).trans (hB t)
      · rw [indicator_of_notMem h]
        show ‖c (β t) (sh V t u) - c (β t) u‖ ≤ _
        rw [hR t (not_le.1 fun h' => h (abs_le.1 h')), map_zero]
        simp
    · rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add_adjacent_intervals (dc.intervalIntegrable (-R) 0) (dc.intervalIntegrable 0 R)]
      have : ∫ t in (0 : ℝ)..R, d t = ∫ t in (-R)..0, d t := by
        rw [← neg_zero, ← intervalIntegral.integral_comp_neg, neg_zero]
        simp only [dn]
      rw [this]; ring
  have e3 : (∫ t in (-R)..0, d t) ^ 2 ≤ R * ∫ t in (-R)..0, d t ^ 2 := by
    set m := ∫ t in (-R)..0, d t with hm
    rcases hR0.eq_or_lt with rfl | hp
    · simp [hm]
    have h0 : 0 ≤ ∫ t in (-R)..0, (R * d t - m) ^ 2 := intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
    have h1 : ∫ t in (-R)..0, (R * d t - m) ^ 2 = R ^ 2 * (∫ t in (-R)..0, d t ^ 2) - 2 * R * m * m + R * m ^ 2 := by
      have : ∀ t, (R * d t - m) ^ 2 = R ^ 2 * d t ^ 2 - 2 * R * m * d t + m ^ 2 := fun t => by ring
      simp only [this]
      rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      · simp [hm]
      all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
    rw [h1] at h0
    nlinarith
  have iw : IntegrableOn (fun t => Real.exp t * d t ^ 2) (Iic 0) := by
    refine ((integrableOn_exp_Iic 0).mul_const ((2 * ‖u‖) ^ 2)).mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
    exact d2 t
  have e4 : ∫ t in (-R)..0, d t ^ 2 ≤ Real.exp R * ∫ t in Iic (0 : ℝ), Real.exp t * d t ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_const_mul]
    refine (setIntegral_mono_on (g := fun t => Real.exp R * (Real.exp t * d t ^ 2)) (dc.pow 2).integrableOn_Ioc
      (Continuous.integrableOn_Ioc (by fun_prop)) measurableSet_Ioc fun t ht => ?_).trans
      (setIntegral_mono_set (iw.const_mul _) (Eventually.of_forall fun t => by positivity) Ioc_subset_Iic_self.eventuallyLE)
    rw [← mul_assoc, ← Real.exp_add]
    exact le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_exp (by linarith [ht.1]))
  calc _ ≤ (2 * B * ∫ t in (-R)..0, d t) ^ 2 := by gcongr
    _ = (2 * B) ^ 2 * (∫ t in (-R)..0, d t) ^ 2 := by ring
    _ ≤ (2 * B) ^ 2 * (R * (Real.exp R * ∫ t in Iic (0 : ℝ), Real.exp t * d t ^ 2)) := by
      gcongr
      exact e3.trans (by gcongr)
    _ = _ := by ring
