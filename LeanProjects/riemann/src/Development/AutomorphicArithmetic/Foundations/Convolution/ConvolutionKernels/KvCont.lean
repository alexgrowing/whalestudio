import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

section

open Filter Topology Set
open scoped ENNReal Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]

private theorem continuous_rightConvolutionCLM (f : CompactlySupportedContinuousMap G ℂ) :
    Continuous (rconvCLM Γ μ f) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds x₀
  have hx₀ : x₀ ∈ V := mem_of_mem_nhds hV
  have hS : IsCompact (V * tsupport (f : G → ℂ)) := hVc.mul f.hasCompactSupport
  obtain ⟨N, hN⟩ := exists_encard_le_of_isCompact Γ hS
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hzero : ∀ x ∈ V, ∀ y ∉ V * tsupport (f : G → ℂ), f (x⁻¹ * y) = 0 := fun x hx y hy => by
    have : x⁻¹ * y ∉ tsupport (f : G → ℂ) := fun h => hy ⟨x, hx, x⁻¹ * y, h, by simp⟩
    exact image_eq_zero_of_notMem_tsupport this
  have hcont : ∀ x : G, Continuous fun y => f (x⁻¹ * y) := fun x =>
    f.continuous.comp (continuous_const_mul x⁻¹)
  let A : G → ℝ≥0∞ := fun x => ∫⁻ y, ‖f (x⁻¹ * y) - f (x₀⁻¹ * y)‖ₑ ^ 2 ∂μ
  have hA : Tendsto A (𝓝 x₀) (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _, 0 ∂μ := by simp
    rw [h0]
    refine tendsto_lintegral_filter_of_dominated_convergence
      ((V * tsupport (f : G → ℂ)).indicator fun _ => ENNReal.ofReal (M + M) ^ 2) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x =>
        ((hcont x).sub (hcont x₀)).measurable.enorm.pow_const 2
    · filter_upwards [hV] with x hx
      refine Eventually.of_forall fun y => ?_
      by_cases hy : y ∈ V * tsupport (f : G → ℂ)
      · rw [indicator_of_mem hy]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (add_le_add (hM _) (hM _)))
      · simp [hzero x hx y hy, hzero x₀ hx₀ y hy]
    · rw [lintegral_indicator hS.measurableSet, lintegral_const]
      exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
        (by rw [Measure.restrict_apply_univ]; exact hS.measure_lt_top)).ne
    · refine Eventually.of_forall fun y => ?_
      have hc : Continuous fun x : G => ‖f (x⁻¹ * y) - f (x₀⁻¹ * y)‖ₑ ^ 2 :=
        (ENNReal.continuous_pow 2).comp
          ((f.continuous.comp (continuous_inv.mul continuous_const)).sub continuous_const).enorm
      simpa using hc.tendsto x₀
  have hkey : ∀ x ∈ V, ∀ φ : Lp ℂ 2 (quotientMeasure Γ μ),
      ‖rconv Γ μ f φ x - rconv Γ μ f φ x₀‖ₑ ^ 2 ≤ (A x * N) * ‖φ‖ₑ ^ 2 := by
    intro x hx φ
    have hsub : rconv Γ μ f φ x - rconv Γ μ f φ x₀ =
        ∫ y, (f (x⁻¹ * y) - f (x₀⁻¹ * y)) * φ (mk Γ y) ∂μ := by
      unfold rconv
      rw [← integral_sub (integrable_rconv Γ μ f φ x) (integrable_rconv Γ μ f φ x₀)]
      simp only [sub_mul]
    have hm1 : AEMeasurable (fun y => ‖f (x⁻¹ * y) - f (x₀⁻¹ * y)‖ₑ) μ :=
      ((hcont x).sub (hcont x₀)).measurable.enorm.aemeasurable
    have hm2 : AEMeasurable
        ((V * tsupport (f : G → ℂ)).indicator fun y => ‖φ (mk Γ y)‖ₑ) μ :=
      ((stronglyMeasurable_lift Γ μ φ).measurable.enorm.indicator hS.measurableSet).aemeasurable
    calc ‖rconv Γ μ f φ x - rconv Γ μ f φ x₀‖ₑ ^ 2
        ≤ (∫⁻ y, ‖f (x⁻¹ * y) - f (x₀⁻¹ * y)‖ₑ *
            (V * tsupport (f : G → ℂ)).indicator (fun y => ‖φ (mk Γ y)‖ₑ) y ∂μ) ^ 2 := by
          rw [hsub]
          gcongr
          refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
          congr 1
          ext y
          by_cases hy : y ∈ V * tsupport (f : G → ℂ)
          · rw [indicator_of_mem hy, enorm_mul]
          · rw [indicator_of_notMem hy, hzero x hx y hy, hzero x₀ hx₀ y hy]
            simp
      _ ≤ A x * ∫⁻ y, (V * tsupport (f : G → ℂ)).indicator
            (fun y => ‖φ (mk Γ y)‖ₑ) y ^ 2 ∂μ :=
          L2Kernel.lintegral_mul_sq_le μ hm1 hm2
      _ = A x * ∫⁻ y in V * tsupport (f : G → ℂ), ‖φ (mk Γ y)‖ₑ ^ 2 ∂μ := by
          congr 1
          rw [← lintegral_indicator hS.measurableSet]
          congr 1
          ext y
          by_cases hy : y ∈ V * tsupport (f : G → ℂ)
          · simp [hy]
          · simp [hy]
      _ ≤ A x * (N * ‖φ‖ₑ ^ 2) := by
          gcongr
          exact lintegral_lift_sq_le Γ μ φ hS.measurableSet hN
      _ = (A x * N) * ‖φ‖ₑ ^ 2 := by rw [mul_assoc]
  have hAN : Tendsto (fun x => A x * N) (𝓝 x₀) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hA (Or.inr (ENNReal.natCast_ne_top N))
  have hlim : Tendsto (fun x => √(A x * N).toReal) (𝓝 x₀) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto _).comp
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hAN)
    rw [ENNReal.toReal_zero, Real.sqrt_zero] at this
    exact this
  have hfin : ∀ᶠ x in 𝓝 x₀, A x * N < 1 := hAN.eventually_lt_const zero_lt_one
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hV, hfin] with x hx hxf
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun φ => ?_
  rw [ContinuousLinearMap.sub_apply, rconvCLM_apply, rconvCLM_apply]
  exact norm_le_of_enorm_sq_le (ne_top_of_lt hxf) (hkey x hx φ)

end

theorem UpperTheory.ConvolutionTheory.K.kvCont :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n),
      Continuous (kv μ f) := by
  intro K _ _ n μ _ f
  exact (InnerProductSpace.toDual ℂ (L2 μ)).symm.continuous.comp
    (continuous_rightConvolutionCLM (Gam K n) μ f)
