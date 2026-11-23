import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Real

namespace GlobalTheory

section Holomorphic

theorem log_norm_le_circleAverage_log_norm {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (h0 : g 0 ≠ 0) : Real.log ‖g 0‖ ≤ Real.circleAverage (fun z => Real.log ‖g z‖) 0 1 := by
  have hg' : AnalyticOnNhd ℂ g (closedBall 0 |(1 : ℝ)|) := by simpa using hg
  rw [hg'.circleAverage_log_norm one_ne_zero h0, le_add_iff_nonneg_left]
  refine finsum_nonneg fun u => ?_
  by_cases hu : u ∈ closedBall (0 : ℂ) |(1 : ℝ)|
  · refine mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg' u) ?_
    rcases eq_or_ne u 0 with rfl | h
    · simp
    · refine Real.log_nonneg ?_
      have h1 : ‖u‖ ≤ 1 := by simpa using hu
      simpa using (one_le_inv₀ (norm_pos_iff.2 h)).2 h1
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

private noncomputable def logGap (M : ℝ) (y : ℂ) : ℝ≥0∞ :=
  if y = 0 then ∞ else ENNReal.ofReal (Real.log M - Real.log ‖y‖)

private theorem measurable_logGap (M : ℝ) : Measurable (logGap M) :=
  Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

private theorem lintegral_logGap_circle_le {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (h0 : g 0 ≠ 0) {M : ℝ} (hM : ∀ z ∈ closedBall (0 : ℂ) 1, ‖g z‖ ≤ M) :
    ∫⁻ t in Ioc 0 (2 * π), logGap M (g (circleMap 0 1 t)) ≤
      ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖g 0‖)) := by
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hne : ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), g (circleMap 0 1 t) ≠ 0 := by
    have h1 := hg.preimage_zero_mem_codiscreteWithin h0 (mem_closedBall_self zero_le_one)
      (isConnected_closedBall zero_le_one)
    have h3 : g ⁻¹' {0}ᶜ ∈ codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|) :=
      codiscreteWithin_mono (by simpa using sphere_subset_closedBall) h1
    exact ae_restrict_le_codiscreteWithin measurableSet_Ioc
      (codiscreteWithin_mono (subset_univ _) (circleMap_preimage_codiscrete one_ne_zero h3))
  have hint : IntegrableOn (fun t => Real.log ‖g (circleMap 0 1 t)‖) (Ioc 0 (2 * π)) := by
    have h1 : CircleIntegrable (fun z => Real.log ‖g z‖) 0 1 :=
      MeromorphicOn.circleIntegrable_log_norm
        (hg.mono (by simpa using sphere_subset_closedBall)).meromorphicOn
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2.le).1 h1
  have hc : IntegrableOn (fun _ : ℝ => Real.log M) (Ioc 0 (2 * π)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hJ := log_norm_le_circleAverage_log_norm hg h0
  rw [Real.circleAverage, intervalIntegral.integral_of_le h2.le, smul_eq_mul,
    le_inv_mul_iff₀ h2] at hJ
  calc ∫⁻ t in Ioc 0 (2 * π), logGap M (g (circleMap 0 1 t))
      = ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (Real.log M - Real.log ‖g (circleMap 0 1 t)‖) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hne] with t ht
        simp [logGap, ht]
    _ = ENNReal.ofReal (∫ t in Ioc 0 (2 * π), (Real.log M - Real.log ‖g (circleMap 0 1 t)‖)) := by
        refine (ofReal_integral_eq_lintegral_ofReal (hc.sub hint) ?_).symm
        filter_upwards [hne] with t ht
        exact sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 ht)
          (hM _ (sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one t))))
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_sub hc hint]
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
          Real.volume_real_Ioc, sub_zero, max_eq_left h2.le, smul_eq_mul]
        linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

theorem integrableOn_log_norm_ball_zero (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℂ}
    {r M : ℝ} (hf : DifferentiableOn ℂ f (ball 0 r)) (hM : ∀ z ∈ ball (0 : E) r, ‖f z‖ ≤ M)
    (h0 : f 0 ≠ 0) :
    (∀ᵐ z ∂(μ.restrict (ball 0 r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball 0 r) μ := by
  classical
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hn : ∀ t, ‖circleMap 0 1 t‖ = 1 := fun t => by simp
  set F : E → ℂ := (ball (0 : E) r).piecewise f 0 with hF
  have hFm : Measurable F :=
    hf.continuousOn.measurable_piecewise continuousOn_const measurableSet_ball
  set G : E → ℝ≥0∞ := (ball (0 : E) r).indicator fun z => logGap M (F z) with hG
  have hGm : Measurable G := ((measurable_logGap M).comp hFm).indicator measurableSet_ball
  have hj : Measurable fun p : ℝ × E => G (circleMap 0 1 p.1 • p.2) := by
    refine hGm.comp (Continuous.measurable ?_)
    exact ((continuous_circleMap 0 1).comp continuous_fst).smul continuous_snd
  have hA : ∫⁻ t in Ioc 0 (2 * π), ∫⁻ z, G (circleMap 0 1 t • z) ∂μ =
      (∫⁻ z in ball 0 r, logGap M (F z) ∂μ) * ENNReal.ofReal (2 * π) := by
    have h4 : ∀ t, ∫⁻ z, G (circleMap 0 1 t • z) ∂μ = ∫⁻ z in ball 0 r, logGap M (F z) ∂μ :=
      fun t => by
        rw [(measurePreserving_smul_of_norm_eq_one μ (hn t)).lintegral_comp hGm, hG,
          lintegral_indicator measurableSet_ball]
    simp [h4]
  have hsm : ∀ z ∈ ball (0 : E) r, ∀ c ∈ closedBall (0 : ℂ) 1, c • z ∈ ball (0 : E) r := by
    intro z hz c hc
    rw [mem_ball_zero_iff] at hz ⊢
    rw [mem_closedBall_zero_iff] at hc
    calc ‖c • z‖ ≤ 1 * ‖z‖ := by rw [norm_smul]; gcongr
      _ < r := by simpa using hz
  have hB : ∫⁻ t in Ioc 0 (2 * π), ∫⁻ z, G (circleMap 0 1 t • z) ∂μ < ∞ := by
    rw [lintegral_lintegral_swap hj.aemeasurable]
    calc ∫⁻ z, ∫⁻ t in Ioc 0 (2 * π), G (circleMap 0 1 t • z) ∂volume ∂μ
        ≤ ∫⁻ z, (ball (0 : E) r).indicator
          (fun _ => ENNReal.ofReal (2 * π * (Real.log M - Real.log ‖f 0‖))) z ∂μ := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ ball (0 : E) r
          · have h5 : ∀ t, G (circleMap 0 1 t • z) = logGap M (f (circleMap 0 1 t • z)) :=
              fun t => by
                have := hsm z hz _ (mem_closedBall_zero_iff.2 (hn t).le)
                rw [hG, indicator_of_mem this, hF, piecewise_eq_of_mem _ _ _ this]
            have h6 : AnalyticOnNhd ℂ (fun c : ℂ => f (c • z)) (closedBall 0 1) := by
              have ho : IsOpen ((fun c : ℂ => c • z) ⁻¹' ball 0 r) :=
                isOpen_ball.preimage (by fun_prop)
              have hd : DifferentiableOn ℂ (fun c : ℂ => f (c • z))
                  ((fun c : ℂ => c • z) ⁻¹' ball 0 r) :=
                hf.comp (by fun_prop) (mapsTo_preimage _ _)
              exact (hd.analyticOnNhd ho).mono fun c hc => hsm z hz c hc
            simp only [indicator_of_mem hz, h5]
            simpa using lintegral_logGap_circle_le h6 (by simpa using h0)
              (fun c hc => hM _ (hsm z hz c hc))
          · have h5 : ∀ t, G (circleMap 0 1 t • z) = 0 := fun t => by
              rw [hG, indicator_of_notMem]
              simpa [norm_smul, hn] using hz
            simp [h5]
      _ < ∞ := by
          rw [lintegral_indicator_const measurableSet_ball]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  rw [hA] at hB
  have hC : ∫⁻ z in ball 0 r, logGap M (F z) ∂μ < ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_left hB.ne (ENNReal.ofReal_pos.2 h2).ne')
  have hFf : F =ᵐ[μ.restrict (ball 0 r)] f := piecewise_ae_eq_restrict measurableSet_ball
  have hne : ∀ᵐ z ∂(μ.restrict (ball 0 r)), f z ≠ 0 := by
    filter_upwards [ae_lt_top ((measurable_logGap M).comp hFm) hC.ne, hFf] with z hz hz' h
    simp [hz', logGap, h] at hz
  refine ⟨hne, ?_⟩
  have hmeas : AEStronglyMeasurable (fun z => Real.log ‖f z‖) (μ.restrict (ball 0 r)) := by
    have : AEMeasurable f (μ.restrict (ball 0 r)) := ⟨F, hFm, hFf.symm⟩
    exact (Real.measurable_log.comp_aemeasurable this.norm).aestronglyMeasurable
  have hc : IntegrableOn (fun _ : E => Real.log M) (ball 0 r) μ :=
    integrableOn_const measure_ball_lt_top.ne
  have hsub : IntegrableOn (fun z => Real.log M - Real.log ‖f z‖) (ball 0 r) μ := by
    refine ⟨aestronglyMeasurable_const.sub hmeas, ?_⟩
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hC
    filter_upwards [hne, hFf, ae_restrict_mem measurableSet_ball] with z hz hz' hzb
    rw [hz', logGap, if_neg hz, Real.enorm_eq_ofReal]
    exact sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 hz) (hM z hzb))
  exact (hc.sub hsub).congr (Eventually.of_forall fun z => by simp)

theorem integrableOn_log_norm_ball (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℂ} {a : E}
    {r M : ℝ} (hf : DifferentiableOn ℂ f (ball a r)) (hM : ∀ z ∈ ball a r, ‖f z‖ ≤ M)
    (h0 : f a ≠ 0) :
    (∀ᵐ z ∂(μ.restrict (ball a r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball a r) μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have hm : MapsTo (fun z : E => z + a) (ball 0 r) (ball a r) := fun z hz => by simpa using hz
  obtain ⟨h1, h2⟩ := integrableOn_log_norm_ball_zero μ (f := fun z => f (z + a)) (r := r) (M := M)
    (hf.comp (by fun_prop) hm) (fun z hz => hM _ (hm hz)) (by simpa using h0)
  have hp : MeasurePreserving (fun z : E => z - a) (μ.restrict (ball a r))
      (μ.restrict (ball 0 r)) := by
    have := (measurePreserving_sub_right μ a).restrict_preimage (s := ball 0 r) measurableSet_ball
    convert this using 2
    ext z
    simp [dist_eq_norm]
  refine ⟨?_, ?_⟩
  · simpa using hp.quasiMeasurePreserving.ae h1
  · simpa [Function.comp_def, IntegrableOn] using hp.integrable_comp_of_integrable h2

theorem exists_integrableOn_log_norm_of_frequently_ne_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℂ} {x : E} (hf : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ f z) (hx : ∃ᶠ z in 𝓝 x, f z ≠ 0) :
    ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball x r) μ := by
  have hb : ∀ᶠ z in 𝓝 x, ‖f z‖ ≤ ‖f x‖ + 1 :=
    (hf.self_of_nhds.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))).mono
      fun _ h => h.le
  obtain ⟨R, hR, hB⟩ := Metric.eventually_nhds_iff_ball.1 (hf.and hb)
  obtain ⟨a, ha, hax⟩ := (hx.and_eventually (ball_mem_nhds x (by positivity : 0 < R / 3))).exists
  have h1 : ball a (2 * R / 3) ⊆ ball x R := ball_subset_ball' (by linarith)
  have h2 : ball x (R / 3) ⊆ ball a (2 * R / 3) :=
    ball_subset_ball' (by rw [dist_comm] at hax; linarith)
  obtain ⟨h3, h4⟩ := integrableOn_log_norm_ball μ (f := f) (a := a) (r := 2 * R / 3)
    (fun z hz => (hB z (h1 hz)).1.differentiableWithinAt) (fun z hz => (hB z (h1 hz)).2) ha
  exact ⟨R / 3, by positivity, ae_restrict_of_ae_restrict_of_subset h2 h3, h4.mono_set h2⟩

theorem locallyIntegrableOn_log_norm_of_frequently_ne_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℂ} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hx : ∀ x ∈ U, ∃ᶠ z in 𝓝 x, f z ≠ 0) :
    (∀ᵐ z ∂(μ.restrict U), f z ≠ 0) ∧ LocallyIntegrableOn (fun z => Real.log ‖f z‖) U μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h : ∀ x ∈ U, ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball x r) μ := fun x hxU =>
    exists_integrableOn_log_norm_of_frequently_ne_zero μ
      (hf.eventually_differentiableAt (hU.mem_nhds hxU)) (hx x hxU)
  refine ⟨?_, fun x hxU => ?_⟩
  · rw [ae_restrict_iff'₀ hU.measurableSet.nullMeasurableSet, ae_iff]
    refine measure_null_of_locally_null _ fun x hx' => ?_
    have hxU : x ∈ U := by
      by_contra hn
      exact hx' fun h => absurd h hn
    obtain ⟨r, hr, h1, -⟩ := h x hxU
    rw [ae_restrict_iff' measurableSet_ball, ae_iff] at h1
    refine ⟨_ ∩ ball x r, inter_mem_nhdsWithin _ (ball_mem_nhds x hr), measure_mono_null ?_ h1⟩
    rintro z ⟨hz, hzb⟩ hz'
    exact hz fun _ => hz' hzb
  · obtain ⟨r, hr, -, h2⟩ := h x hxU
    exact ⟨ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr), h2⟩

theorem exists_integrableOn_log_norm_div (μ : Measure E) [μ.IsAddHaarMeasure]
    {g h : E → ℂ} {x : E} (hg : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ g z)
    (hh : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ h z) (hg0 : ∃ᶠ z in 𝓝 x, g z ≠ 0)
    (hh0 : ∃ᶠ z in 𝓝 x, h z ≠ 0) :
    ∃ r > 0, (∀ᵐ z ∂(μ.restrict (ball x r)), g z ≠ 0 ∧ h z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖g z / h z‖) (ball x r) μ := by
  obtain ⟨r, hr, h1, h2⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero μ hg hg0
  obtain ⟨s, hs, h3, h4⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero μ hh hh0
  have e1 : ball x (min r s) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  have e2 : ball x (min r s) ⊆ ball x s := ball_subset_ball (min_le_right _ _)
  have h5 := (ae_restrict_of_ae_restrict_of_subset e1 h1).and
    (ae_restrict_of_ae_restrict_of_subset e2 h3)
  refine ⟨min r s, lt_min hr hs, h5, ((h2.mono_set e1).sub (h4.mono_set e2)).congr ?_⟩
  filter_upwards [h5] with z hz
  simp [Real.log_div, hz.1, hz.2]

end Holomorphic

section Coordinates

open Bornology

variable {ι : Type*} [Fintype ι]

variable {F : Type*} [NormedAddCommGroup F]

end Coordinates

end GlobalTheory
