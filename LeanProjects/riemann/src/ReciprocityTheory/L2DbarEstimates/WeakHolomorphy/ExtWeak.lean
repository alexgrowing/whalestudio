import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtCut
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeak
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollifyEqConvolution
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtWeakA

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff

variable {n : ℕ}

theorem dbarDir_continuous_hasCompactSupport {g : V n → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (v : V n) :
    Continuous (fun z => dbarDir g z v) ∧ HasCompactSupport (fun z => dbarDir g z v) := by
  have hd : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  refine ⟨?_, ?_⟩
  · unfold dbarDir
    exact (hd.clm_apply continuous_const).sub
      (continuous_const.mul (hd.clm_apply continuous_const))
  · unfold dbarDir
    exact (hc.fderiv_apply ℝ (I • v)).sub ((hc.fderiv_apply ℝ v).mul_left)

theorem integrableOn_mul_of_sq {W : Set (V n)} {u h : V n → ℂ}
    (hum : AEStronglyMeasurable u (volume.restrict W)) (hu2 : IntegrableOn (fun z => ‖u z‖ ^ 2) W)
    (hc : Continuous h) (hs : HasCompactSupport h) : IntegrableOn (fun z => u z * h z) W := by
  have hh2 : Integrable (fun z => ‖h z‖ ^ 2) :=
    (hc.norm.pow 2).integrable_of_hasCompactSupport
      (hs.mono (fun z hz => by
        rw [Function.mem_support] at hz ⊢
        intro h0
        exact hz (by simp [h0])))
  refine Integrable.mono' ((hu2.add hh2.integrableOn).div_const 2)
    (hum.mul hc.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  simp only [Pi.add_apply, norm_mul]
  nlinarith [sq_nonneg (‖u z‖ - ‖h z‖), norm_nonneg (u z), norm_nonneg (h z)]

theorem measurableSet_ge_of_continuousOn {W : Set (V n)} (hW : IsOpen W) {f : V n → ℝ}
    (hf : ContinuousOn f W) (c : ℝ) : MeasurableSet {z | z ∈ W ∧ c ≤ f z} := by
  have h1 : IsOpen (W ∩ f ⁻¹' Set.Iio c) := hf.isOpen_inter_preimage hW isOpen_Iio
  have h2 : {z | z ∈ W ∧ c ≤ f z} = W \ (W ∩ f ⁻¹' Set.Iio c) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Iio, not_and, not_lt]
    exact ⟨fun ⟨a, b⟩ => ⟨a, fun _ => b⟩, fun ⟨a, b⟩ => ⟨a, b a⟩⟩
  rw [h2]
  exact hW.measurableSet.diff h1.measurableSet

theorem tendsto_setLIntegral_band {W : Set (V n)} (hW : IsOpen W) {f : V n → ℝ}
    (hf : ContinuousOn f W) {φ : V n → ℝ≥0∞} (hφ : ∫⁻ z in W, φ z < ⊤) :
    Tendsto (fun k : ℕ => ∫⁻ z in {z | z ∈ W ∧ (k : ℝ) + 1 ≤ f z}, φ z) atTop (𝓝 0) := by
  set A : ℕ → Set (V n) := fun k => {z | z ∈ W ∧ (k : ℝ) + 1 ≤ f z} with hA
  have hmeas : ∀ k, MeasurableSet (A k) := fun k => measurableSet_ge_of_continuousOn hW hf _
  have hanti : Antitone A := by
    intro i j hij z hz
    refine ⟨hz.1, le_trans ?_ hz.2⟩
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have hempty : (⋂ k, A k) = ∅ := by
    ext z
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨k, hk⟩ := exists_nat_gt (f z)
    exact ⟨k, fun h => by have := h.2; linarith⟩
  have hfin : ∃ k, volume.withDensity φ (A k) ≠ ⊤ := ⟨0, by
    rw [withDensity_apply _ (hmeas 0)]
    exact (lt_of_le_of_lt (lintegral_mono_set (fun z hz => hz.1)) hφ).ne⟩
  have h := tendsto_measure_iInter_atTop (fun k => (hmeas k).nullMeasurableSet) hanti hfin
  rw [hempty, measure_empty] at h
  refine h.congr (fun k => ?_)
  simp only [Function.comp_apply]
  exact withDensity_apply _ (hmeas k)

noncomputable def extErr (F : V n → ℂ) (k : ℝ) (v z : V n) : ℂ :=
  (fderiv ℝ (extCut F k) z (I • v) : ℂ) - I * (fderiv ℝ (extCut F k) z v : ℂ)

theorem extErr_le {F g u : V n → ℂ} {k C0 Mg : ℝ} (hk : 0 < k) (hC0 : 0 ≤ C0)
    (hC0b : ∀ t, ‖deriv extCh t‖ ≤ C0) (hMg : ∀ z, ‖g z‖ ≤ Mg) {z : V n} (v : V n)
    (hFd : DifferentiableAt ℝ F z) (hz : F z ≠ 0) :
    ‖u z * g z * extErr F k v z‖ₑ ≤ ENNReal.ofReal (Mg * (2 * ‖v‖) * C0 * k⁻¹) *
      (tsupport g ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
        -Real.log (‖F z‖ ^ 2) ≤ 2 * k}).indicator
        (fun z => ‖u z‖ₑ * ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ) z := by
  classical
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg z)
  by_cases hmem : z ∈ tsupport g ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
      -Real.log (‖F z‖ ^ 2) ≤ 2 * k}
  · rw [Set.indicator_apply, if_pos hmem]
    have hD := norm_fderiv_logCutoff_le hk hC0b hFd hz
    have hE : ‖extErr F k v z‖ ≤ 2 * ‖v‖ * ‖fderiv ℝ (extCut F k) z‖ := by
      unfold extErr
      calc _ ≤ ‖((fderiv ℝ (extCut F k) z (I • v) : ℝ) : ℂ)‖ +
            ‖I * ((fderiv ℝ (extCut F k) z v : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ = ‖fderiv ℝ (extCut F k) z (I • v)‖ + ‖fderiv ℝ (extCut F k) z v‖ := by
            rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real]
        _ ≤ ‖fderiv ℝ (extCut F k) z‖ * ‖I • v‖ + ‖fderiv ℝ (extCut F k) z‖ * ‖v‖ :=
            add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
        _ = 2 * ‖v‖ * ‖fderiv ℝ (extCut F k) z‖ := by
            rw [norm_smul, Complex.norm_I, one_mul]; ring
    have hK : 0 ≤ Mg * (2 * ‖v‖) * C0 * k⁻¹ :=
      mul_nonneg (mul_nonneg (mul_nonneg hMg0 (by positivity)) hC0) (inv_nonneg.mpr hk.le)
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul hK]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, norm_mul]
    have hE' : ‖extErr F k v z‖ ≤ 2 * ‖v‖ * (C0 * k⁻¹ *
        ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖) :=
      hE.trans (mul_le_mul_of_nonneg_left hD (by positivity))
    calc ‖u z‖ * ‖g z‖ * ‖extErr F k v z‖ ≤ ‖u z‖ * Mg * (2 * ‖v‖ * (C0 * k⁻¹ *
          ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖)) := by
          gcongr
          exact hMg z
      _ = _ := by ring
  · rw [Set.indicator_apply, if_neg hmem, mul_zero, nonpos_iff_eq_zero, enorm_eq_zero]
    by_cases hzt : z ∈ tsupport g
    · have h2 : ¬ (k ≤ -Real.log (‖F z‖ ^ 2) ∧ -Real.log (‖F z‖ ^ 2) ≤ 2 * k) :=
        fun hb => hmem ⟨hzt, hz, hb⟩
      have h3 := fderiv_logCutoff_eq_zero hk hFd hz h2
      simp [extErr, h3]
    · rw [image_eq_zero_of_notMem_tsupport hzt]
      simp

private theorem locallyIntegrableOn_indicator_of_sq_integrableOn {Ω W : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω) (hW : MeasurableSet W)
    (hum : AEStronglyMeasurable u (volume.restrict W))
    (hu2 : IntegrableOn (fun z => ‖u z‖ ^ 2) W) : LocallyIntegrableOn (W.indicator u) Ω volume := by
  intro x hx
  obtain ⟨r, hr, -⟩ := Metric.isOpen_iff.mp hΩ x hx
  refine ⟨ball x r, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hr), ?_⟩
  show Integrable (W.indicator u) (volume.restrict (ball x r))
  rw [integrable_indicator_iff hW, IntegrableOn, Measure.restrict_restrict hW]
  have hfin : volume (W ∩ ball x r) < ⊤ :=
    (measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top
  haveI : IsFiniteMeasure (volume.restrict (W ∩ ball x r)) :=
    isFiniteMeasure_restrict.mpr hfin.ne
  refine Integrable.mono' (((hu2.mono_set Set.inter_subset_left).add
    (integrable_const (1 : ℝ))).div_const 2)
    (hum.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)) ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖u z‖ - 1), norm_nonneg (u z)]

private theorem bound_lemma_3 {Ω : Set (V n)} {F u g : V n → ℂ} {C0 Mg : ℝ} {C : ℝ≥0∞} (v : V n)
    (j : ℕ) (hsm : ∀ z ∈ Ω, ContDiffAt ℝ ∞ F z) (hgΩ : tsupport g ⊆ Ω)
    (hMg : ∀ z, ‖g z‖ ≤ Mg) (hMg0 : 0 ≤ Mg) (hC0 : 0 ≤ C0) (hC0b : ∀ t, ‖deriv extCh t‖ ≤ C0)
    (hWm : MeasurableSet (Ω \ {z | F z = 0}))
    (hSm : ∀ k : ℝ, MeasurableSet (tsupport g ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
      -Real.log (‖F z‖ ^ 2) ≤ 2 * k}))
    (hTm : ∀ k : ℝ, MeasurableSet {z | z ∈ Ω \ {z | F z = 0} ∧ k ≤ -Real.log (‖F z‖ ^ 2)})
    (hCb : ∀ k : ℝ, 1 ≤ k → ∫⁻ z in tsupport g ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
      -Real.log (‖F z‖ ^ 2) ≤ 2 * k}, ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2 ≤
        C * ENNReal.ofReal (k ^ 2))
    (hum : AEStronglyMeasurable u (volume.restrict (Ω \ {z | F z = 0}))) :
    ‖∫ z in Ω \ {z | F z = 0}, u z * g z * extErr F ((j : ℝ) + 1) v z‖ₑ ≤
      (ENNReal.ofReal (Mg * (2 * ‖v‖) * C0) * C ^ (1 / 2 : ℝ)) *
        (∫⁻ z in {z | z ∈ Ω \ {z | F z = 0} ∧ (j : ℝ) + 1 ≤ -Real.log (‖F z‖ ^ 2)},
          ‖u z‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  classical
  have hk : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hk1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
  obtain ⟨S, hS⟩ : ∃ S : Set (V n), S = tsupport g ∩ {z | F z ≠ 0 ∧
      (j : ℝ) + 1 ≤ -Real.log (‖F z‖ ^ 2) ∧ -Real.log (‖F z‖ ^ 2) ≤ 2 * ((j : ℝ) + 1)} := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Set (V n), T = {z | z ∈ Ω \ {z | F z = 0} ∧
      (j : ℝ) + 1 ≤ -Real.log (‖F z‖ ^ 2)} := ⟨_, rfl⟩
  have hSm' : MeasurableSet S := by rw [hS]; exact hSm _
  have hTm' : MeasurableSet T := by rw [hT]; exact hTm _
  rw [← hT]
  have hK : 0 ≤ Mg * (2 * ‖v‖) * C0 * ((j : ℝ) + 1)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg hMg0 (by positivity)) hC0) (inv_nonneg.mpr hk.le)
  have step1 := enorm_integral_le_lintegral_enorm
    (μ := volume.restrict (Ω \ {z | F z = 0})) (fun z => u z * g z * extErr F ((j : ℝ) + 1) v z)
  have step2 : ∫⁻ z in Ω \ {z | F z = 0}, ‖u z * g z * extErr F ((j : ℝ) + 1) v z‖ₑ ≤
      ∫⁻ z in Ω \ {z | F z = 0}, ENNReal.ofReal (Mg * (2 * ‖v‖) * C0 * ((j : ℝ) + 1)⁻¹) *
        (S.indicator (fun z => ‖u z‖ₑ) z *
          S.indicator (fun z => ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ) z) := by
    refine lintegral_mono_ae (ae_restrict_of_forall_mem hWm (fun z hz => ?_))
    have h := extErr_le (u := u) hk hC0 hC0b hMg v ((hsm z hz.1).differentiableAt (by simp)) hz.2
    rw [← hS] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS, Set.indicator_of_mem hzS, Set.indicator_of_mem hzS]
    · rw [Set.indicator_apply, if_neg hzS, Set.indicator_apply, if_neg hzS, zero_mul]
  have step3 := lintegral_const_mul' (μ := volume.restrict (Ω \ {z | F z = 0}))
    (ENNReal.ofReal (Mg * (2 * ‖v‖) * C0 * ((j : ℝ) + 1)⁻¹))
    (fun z => S.indicator (fun z => ‖u z‖ₑ) z *
      S.indicator (fun z => ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ) z)
    ENNReal.ofReal_ne_top
  have step4 := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ω \ {z | F z = 0}))
    Real.HolderConjugate.two_two ((hum.enorm).indicator hSm')
    ((measurable_fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2))).enorm.aemeasurable.indicator hSm')
  have step5 : ∫⁻ z in Ω \ {z | F z = 0}, S.indicator (fun z => ‖u z‖ₑ) z ^ (2 : ℝ) ≤
      ∫⁻ z in T, ‖u z‖ₑ ^ 2 := by
    calc ∫⁻ z in Ω \ {z | F z = 0}, S.indicator (fun z => ‖u z‖ₑ) z ^ (2 : ℝ) ≤
          ∫⁻ z in Ω \ {z | F z = 0}, T.indicator (fun z => ‖u z‖ₑ ^ 2) z := by
          refine lintegral_mono (fun z => ?_)
          by_cases hzS : z ∈ S
          · have hzT : z ∈ T := by
              rw [hS] at hzS
              rw [hT]
              exact ⟨⟨hgΩ hzS.1, hzS.2.1⟩, hzS.2.2.1⟩
            rw [Set.indicator_of_mem hzS, Set.indicator_of_mem hzT, ENNReal.rpow_two]
          · rw [Set.indicator_apply, if_neg hzS, ENNReal.zero_rpow_of_pos (by norm_num)]
            exact zero_le
      _ ≤ ∫⁻ z, T.indicator (fun z => ‖u z‖ₑ ^ 2) z := setLIntegral_le_lintegral _ _
      _ = ∫⁻ z in T, ‖u z‖ₑ ^ 2 := lintegral_indicator hTm' _
  have step6 : ∫⁻ z in Ω \ {z | F z = 0},
      S.indicator (fun z => ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ) z ^ (2 : ℝ) ≤
      C * ENNReal.ofReal (((j : ℝ) + 1) ^ 2) := by
    calc ∫⁻ z in Ω \ {z | F z = 0},
          S.indicator (fun z => ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ) z ^ (2 : ℝ) ≤
          ∫⁻ z in Ω \ {z | F z = 0},
            S.indicator (fun z => ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2) z := by
          refine lintegral_mono (fun z => ?_)
          by_cases hzS : z ∈ S
          · rw [Set.indicator_of_mem hzS, Set.indicator_of_mem hzS, ENNReal.rpow_two]
          · rw [Set.indicator_apply, if_neg hzS, Set.indicator_apply, if_neg hzS,
              ENNReal.zero_rpow_of_pos (by norm_num)]
      _ ≤ ∫⁻ z, S.indicator (fun z => ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2) z :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ z in S, ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2 := lintegral_indicator hSm' _
      _ ≤ C * ENNReal.ofReal (((j : ℝ) + 1) ^ 2) := by rw [hS]; exact hCb _ hk1
  have hsq : (((j : ℝ) + 1) ^ 2) ^ (1 / 2 : ℝ) = (j : ℝ) + 1 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hk.le]
  have hcomb : ENNReal.ofReal (Mg * (2 * ‖v‖) * C0 * ((j : ℝ) + 1)⁻¹) *
      ENNReal.ofReal ((j : ℝ) + 1) = ENNReal.ofReal (Mg * (2 * ‖v‖) * C0) := by
    rw [← ENNReal.ofReal_mul hK]
    congr 1
    field_simp
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ = _ := step3
    _ ≤ ENNReal.ofReal (Mg * (2 * ‖v‖) * C0 * ((j : ℝ) + 1)⁻¹) *
        ((∫⁻ z in T, ‖u z‖ₑ ^ 2) ^ (1 / 2 : ℝ) *
          (C * ENNReal.ofReal (((j : ℝ) + 1) ^ 2)) ^ (1 / 2 : ℝ)) := by
        refine mul_le_mul' le_rfl (step4.trans ?_)
        exact mul_le_mul' (ENNReal.rpow_le_rpow step5 (by norm_num))
          (ENNReal.rpow_le_rpow step6 (by norm_num))
    _ = (ENNReal.ofReal (Mg * (2 * ‖v‖) * C0 * ((j : ℝ) + 1)⁻¹) *
          ENNReal.ofReal ((j : ℝ) + 1)) * C ^ (1 / 2 : ℝ) *
        (∫⁻ z in T, ‖u z‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), hsq]
        ring
    _ = _ := by rw [hcomb]

private theorem main_lemma_2 {Ω : Set (V n)} {F u g : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) (hsm : ∀ z ∈ Ω, ContDiffAt ℝ ∞ F z)
    (hu : DifferentiableOn ℂ u (Ω \ {z | F z = 0}))
    (hu2 : IntegrableOn (fun z => ‖u z‖ ^ 2) (Ω \ {z | F z = 0}))
    (hg : IsTest Ω g) (v : V n) :
    ∫ z in Ω \ {z | F z = 0}, u z * dbarDir g z v = 0 := by
  classical
  set W := Ω \ {z | F z = 0} with hWdef
  have hWsub : W ⊆ Ω := Set.diff_subset
  have hWo : IsOpen W := by
    have e : W = Ω ∩ F ⁻¹' {0}ᶜ := by ext z; simp [hWdef]
    rw [e]
    exact hF.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton
  have hWm : MeasurableSet W := hWo.measurableSet
  have hum : AEStronglyMeasurable u (volume.restrict W) := hu.continuousOn.aestronglyMeasurable hWm
  obtain ⟨hgc, hgs, hgΩ⟩ := hg
  have hd1 := dbarDir_continuous_hasCompactSupport hgc hgs v
  have hud : IntegrableOn (fun z => u z * dbarDir g z v) W :=
    integrableOn_mul_of_sq hum hu2 hd1.1 hd1.2
  have hk : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 1 := fun j => by positivity
  have hmeasA : ∀ j : ℕ, AEStronglyMeasurable
      (fun z => u z * (extCut F ((j : ℝ) + 1) z : ℂ) * dbarDir g z v) (volume.restrict W) := by
    intro j
    have hχ : ContinuousOn (fun z => (extCut F ((j : ℝ) + 1) z : ℂ)) W := fun z hz =>
      (Complex.continuous_ofReal.continuousAt.comp
        ((contDiffAt_logCutoff (hk j) (hsm z hz.1)).continuousAt)).continuousWithinAt
    exact (hum.mul (hχ.aestronglyMeasurable hWm)).mul hd1.1.aestronglyMeasurable
  have hboundA : ∀ j : ℕ, ∀ z, ‖u z * (extCut F ((j : ℝ) + 1) z : ℂ) * dbarDir g z v‖ ≤
      ‖u z * dbarDir g z v‖ := by
    intro j z
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (logCutoff_nonneg _ _ _)]
    have h1 := logCutoff_le_one F ((j : ℝ) + 1) z
    have h2 := logCutoff_nonneg F ((j : ℝ) + 1) z
    have h3 := mul_nonneg (norm_nonneg (u z)) (norm_nonneg (dbarDir g z v))
    nlinarith
  have hA : Tendsto (fun j : ℕ => ∫ z in W, u z * (extCut F ((j : ℝ) + 1) z : ℂ) * dbarDir g z v)
      atTop (𝓝 (∫ z in W, u z * dbarDir g z v)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖u z * dbarDir g z v‖)
      hmeasA hud.norm (fun j => Filter.Eventually.of_forall (hboundA j)) ?_
    refine ae_restrict_of_forall_mem hWm (fun z hz => ?_)
    have hFz : F z ≠ 0 := hz.2
    obtain ⟨N, hN⟩ := exists_nat_ge (-Real.log (‖F z‖ ^ 2))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    have hNj : (N : ℝ) ≤ j := by exact_mod_cast hj
    rw [logCutoff_eq_one (hk j) hFz (by linarith)]
    simp
  have hAB : ∀ j : ℕ, (∫ z in W, u z * (extCut F ((j : ℝ) + 1) z : ℂ) * dbarDir g z v) =
      -∫ z in W, u z * g z * extErr F ((j : ℝ) + 1) v z := by
    intro j
    have hk' := hk j
    have htest := isTest_logCutoff_mul hsm hk' ⟨hgc, hgs, hgΩ⟩
    have h0 := (holoWeak n W u hWo hu).2 _ htest v
    have hpt : ∀ z ∈ W, u z * dbarDir (fun w => (extCut F ((j : ℝ) + 1) w : ℂ) * g w) z v =
        u z * (extCut F ((j : ℝ) + 1) z : ℂ) * dbarDir g z v +
          u z * g z * extErr F ((j : ℝ) + 1) v z := by
      intro z hz
      rw [dbarDir_extensionCutoff_mul v ((contDiffAt_logCutoff hk' (hsm z hz.1)).differentiableAt (by simp))
        (hgc.differentiable (by simp) z)]
      simp only [extErr]
      ring
    have hI1 : IntegrableOn
        (fun z => u z * dbarDir (fun w => (extCut F ((j : ℝ) + 1) w : ℂ) * g w) z v) W := by
      have h := dbarDir_continuous_hasCompactSupport htest.1 htest.2.1 v
      exact integrableOn_mul_of_sq hum hu2 h.1 h.2
    have hI2 : IntegrableOn (fun z => u z * (extCut F ((j : ℝ) + 1) z : ℂ) * dbarDir g z v) W :=
      Integrable.mono' hud.norm (hmeasA j) (Filter.Eventually.of_forall (hboundA j))
    have hsplit : ∫ z in W, u z * g z * extErr F ((j : ℝ) + 1) v z =
        (∫ z in W, u z * dbarDir (fun w => (extCut F ((j : ℝ) + 1) w : ℂ) * g w) z v) -
          ∫ z in W, u z * (extCut F ((j : ℝ) + 1) z : ℂ) * dbarDir g z v := by
      rw [← integral_sub hI1 hI2]
      refine setIntegral_congr_fun hWm (fun z hz => ?_)
      rw [hpt z hz]
      ring
    rw [hsplit, h0]
    ring

  obtain ⟨C0, hC0, hC0b⟩ := exists_deriv_extCh_le
  obtain ⟨Mg, hMg⟩ := hgc.continuous.bounded_above_of_compact_support hgs
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
  obtain ⟨C, hC, hCb⟩ := ext_cut hΩ hF hgs hgΩ
  have hfc : ContinuousOn (fun z => -Real.log (‖F z‖ ^ 2)) W := by
    refine ContinuousOn.neg (ContinuousOn.log ((hF.continuousOn.mono hWsub).norm.pow 2) ?_)
    intro z hz
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz.2)
  have hm2 : ∫⁻ z in W, ‖u z‖ₑ ^ 2 < ⊤ := by
    have e : ∀ z, ‖‖u z‖ ^ 2‖ₑ = ‖u z‖ₑ ^ 2 := fun z => by rw [enorm_pow, enorm_norm]
    have h := hu2.2
    unfold HasFiniteIntegral at h
    simpa only [e] using h
  have hmass : Tendsto (fun j : ℕ => ∫⁻ z in {z | z ∈ W ∧ (j : ℝ) + 1 ≤ -Real.log (‖F z‖ ^ 2)},
      ‖u z‖ₑ ^ 2) atTop (𝓝 0) := tendsto_setLIntegral_band hWo hfc hm2
  have hSm : ∀ k : ℝ, MeasurableSet (tsupport g ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
      -Real.log (‖F z‖ ^ 2) ≤ 2 * k}) := by
    intro k
    have e : tsupport g ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
        -Real.log (‖F z‖ ^ 2) ≤ 2 * k} = tsupport g ∩
        ({z | z ∈ W ∧ k ≤ -Real.log (‖F z‖ ^ 2)} ∩
          {z | z ∈ W ∧ -(2 * k) ≤ - -Real.log (‖F z‖ ^ 2)}) := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hz, hF0, h1, h2⟩
        have hzW : z ∈ W := ⟨hgΩ hz, hF0⟩
        exact ⟨hz, ⟨hzW, h1⟩, hzW, by linarith⟩
      · rintro ⟨hz, ⟨hzW, h1⟩, _, h2⟩
        exact ⟨hz, hzW.2, h1, by linarith⟩
    rw [e]
    exact (isClosed_tsupport g).measurableSet.inter
      ((measurableSet_ge_of_continuousOn hWo hfc k).inter
        (measurableSet_ge_of_continuousOn hWo hfc.neg (-(2 * k))))
  have hbound : ∀ j : ℕ, ‖∫ z in W, u z * g z * extErr F ((j : ℝ) + 1) v z‖ₑ ≤
      (ENNReal.ofReal (Mg * (2 * ‖v‖) * C0) * C ^ (1 / 2 : ℝ)) *
        (∫⁻ z in {z | z ∈ W ∧ (j : ℝ) + 1 ≤ -Real.log (‖F z‖ ^ 2)}, ‖u z‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
    fun j => bound_lemma_3 v j hsm hgΩ hMg hMg0 hC0 hC0b hWm hSm
      (fun k => measurableSet_ge_of_continuousOn hWo hfc k) hCb hum
  have hR : Tendsto (fun j : ℕ => (ENNReal.ofReal (Mg * (2 * ‖v‖) * C0) * C ^ (1 / 2 : ℝ)) *
      (∫⁻ z in {z | z ∈ W ∧ (j : ℝ) + 1 ≤ -Real.log (‖F z‖ ^ 2)}, ‖u z‖ₑ ^ 2) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ =>
        (∫⁻ z in {z | z ∈ W ∧ (j : ℝ) + 1 ≤ -Real.log (‖F z‖ ^ 2)}, ‖u z‖ₑ ^ 2) ^ (1 / 2 : ℝ))
        atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hmass
      rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    have hne : ENNReal.ofReal (Mg * (2 * ‖v‖) * C0) * C ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC.ne)
    have := ENNReal.Tendsto.const_mul h1 (Or.inr hne)
    rwa [mul_zero] at this
  have hBe : Tendsto (fun j : ℕ => ‖∫ z in W, u z * g z * extErr F ((j : ℝ) + 1) v z‖ₑ)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR (fun _ => zero_le) hbound
  have hB : Tendsto (fun j : ℕ => ∫ z in W, u z * g z * extErr F ((j : ℝ) + 1) v z)
      atTop (𝓝 0) :=
    tendsto_iff_edist_tendsto_0.mpr (by simpa only [edist_zero_right] using hBe)
  have hA' : Tendsto (fun j : ℕ => ∫ z in W, u z * (extCut F ((j : ℝ) + 1) z : ℂ) * dbarDir g z v)
      atTop (𝓝 0) := by
    have h := hB.neg
    rw [neg_zero] at h
    exact h.congr (fun j => (hAB j).symm)
  exact tendsto_nhds_unique hA hA'

theorem extWeak_of_smooth {Ω : Set (V n)} {F u : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) (hsm : ∀ z ∈ Ω, ContDiffAt ℝ ∞ F z)
    (hu : DifferentiableOn ℂ u (Ω \ {z | F z = 0}))
    (hu2 : IntegrableOn (fun z => ‖u z‖ ^ 2) (Ω \ {z | F z = 0})) :
    WeakHolo Ω ((Ω \ {z | F z = 0}).indicator u) := by
  classical
  have hWo : IsOpen (Ω \ {z | F z = 0}) := by
    have e : Ω \ {z | F z = 0} = Ω ∩ F ⁻¹' {0}ᶜ := by ext z; simp
    rw [e]
    exact hF.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton
  have hWm : MeasurableSet (Ω \ {z | F z = 0}) := hWo.measurableSet
  have hum : AEStronglyMeasurable u (volume.restrict (Ω \ {z | F z = 0})) :=
    hu.continuousOn.aestronglyMeasurable hWm
  refine ⟨locallyIntegrableOn_indicator_of_sq_integrableOn hΩ hWm hum hu2, ?_⟩
  intro g hg v
  have hred : ∫ z in Ω, (Ω \ {z | F z = 0}).indicator u z * dbarDir g z v =
      ∫ z in Ω \ {z | F z = 0}, u z * dbarDir g z v := by
    have e : (fun z => (Ω \ {z | F z = 0}).indicator u z * dbarDir g z v) =
        (Ω \ {z | F z = 0}).indicator (fun z => u z * dbarDir g z v) := by
      funext z
      by_cases hz : z ∈ Ω \ {z | F z = 0}
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_apply, if_neg hz, Set.indicator_apply, if_neg hz, zero_mul]
    rw [e, setIntegral_indicator hWm, Set.inter_eq_right.mpr Set.diff_subset]
  rw [hred]
  exact main_lemma_2 hΩ hF hsm hu hu2 hg v

theorem extWeak : ExtWeakStatement := by
  intro n Ω F u hΩ hF hu hu2
  exact extWeak_of_smooth hΩ hF
    (fun z hz => (holo_contDiffOn hΩ hF).contDiffAt (hΩ.mem_nhds hz)) hu hu2

end ReciprocityTheory.L2DbarEstimates.C
