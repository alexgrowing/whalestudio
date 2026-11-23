import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HormanderEstimateOnBallConstLeviBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloAeEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricSeriesSectionsL2LimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloSectionAeEqOfBallCoverStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem ofReal_sq_sub_mul_le (x y z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ENNReal.ofReal (‖x - y‖ ^ 2 * ρ) ≤
      2 * ENNReal.ofReal (‖z - x‖ ^ 2 * ρ) + 2 * ENNReal.ofReal (‖z - y‖ ^ 2 * ρ) := by
  have h1 : ‖x - y‖ ≤ ‖z - x‖ + ‖z - y‖ := by
    calc ‖x - y‖ = ‖(z - y) - (z - x)‖ := by congr 1; ring
      _ ≤ ‖z - y‖ + ‖z - x‖ := norm_sub_le _ _
      _ = ‖z - x‖ + ‖z - y‖ := add_comm _ _
  have h2 : ‖x - y‖ ^ 2 ≤ 2 * ‖z - x‖ ^ 2 + 2 * ‖z - y‖ ^ 2 := by
    nlinarith [norm_nonneg (x - y), norm_nonneg (z - x), norm_nonneg (z - y),
      sq_nonneg (‖z - x‖ - ‖z - y‖)]
  have h3 : ‖x - y‖ ^ 2 * ρ ≤ 2 * (‖z - x‖ ^ 2 * ρ) + 2 * (‖z - y‖ ^ 2 * ρ) := by
    have := mul_le_mul_of_nonneg_right h2 hρ
    linarith
  calc ENNReal.ofReal (‖x - y‖ ^ 2 * ρ)
      ≤ ENNReal.ofReal (2 * (‖z - x‖ ^ 2 * ρ) + 2 * (‖z - y‖ ^ 2 * ρ)) := ENNReal.ofReal_le_ofReal h3
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
      simp

theorem exists_isSec_of_rapid_cauchy : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (t K : ℝ) (F : ℕ → ι → Y → ℂ), 0 < t → CurvGe C la t → 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → Tendsto (fun m => n1 C la (F m)) atTop (𝓝 0) → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + la) G ∧ n0 A la (F 0 - G) ≤ ENNReal.ofReal (4 * K) := by
  intro n Y _ _ _ _ _ ι La _ A C la t K F ht hcurv hK hF hcau hn1
  obtain ⟨f, hfc, hfm, hfn⟩ := GlobalTheory.T.geometric_series_sections_l2_limit n Y ι La A la F K hK hF hcau

  have hWsub : ∀ a, ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
    fun a => ball_subset_closedBall.trans (C.sub a)

  have hH : ∀ m a, ∃ u : V n → ℂ, DifferentiableOn ℂ u (ball (C.c a) (C.r a)) ∧
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤ ENNReal.ofReal t⁻¹ * n1 C la (F m) := by
    intro m a
    obtain ⟨u, hu, hle⟩ := GlobalTheory.T.hormander_estimate_on_ball_const_levi_bound n (C.c a) (C.r a) t
      (fun w => A.ph la (C.idx a) ((A.chart (C.idx a)).symm w)) (F m (C.idx a) ∘ (A.chart (C.idx a)).symm) ht
      ((A.smooth_ph la (C.idx a)).mono (hWsub a)) (((hF m).1 (C.idx a)).mono (hWsub a))
      (by
        intro v hv ξ
        have := hcurv a v hv ξ
        simp only [WeightedAtlas.leviAt] at this
        rwa [(A.chart (C.idx a)).right_inv (hWsub a hv)] at this)
    refine ⟨u, hu, hle.trans ?_⟩
    gcongr
    unfold n1
    exact Finset.single_le_sum (f := fun a => ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
      ((∑ j, ‖wdb n j (F m (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) (fun _ _ => bot_le) (Finset.mem_univ a)
  choose u hu hule using hH

  have hD : ∀ m a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) -
      f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
      ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
    intro m a
    have e := GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx a) (ball (C.c a) (C.r a)) (F m - f) measurableSet_ball (hWsub a)
      (by
        intro y hy _
        simp only [Pi.sub_apply]
        rw [(hF m).2 _ _ _ (A.mem_pick y) hy, hfc _ _ _ (A.mem_pick y) hy]
        ring)
      (((((hF m).1 (C.idx a)).continuousOn.aemeasurable (A.chart (C.idx a)).open_target.measurableSet).sub
        (hfm (C.idx a))).mono_measure (Measure.restrict_mono (hWsub a) le_rfl))
    refine le_trans (le_of_eq e.symm) ?_
    exact (setLIntegral_le_lintegral _ _).trans (hfn m)
  have hT : Tendsto (fun m : ℕ => 2 * ENNReal.ofReal (4 * K / 4 ^ m) +
      2 * (ENNReal.ofReal t⁻¹ * n1 C la (F m))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ENNReal.ofReal (4 * K / 4 ^ m)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal
        (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
    have h2 : Tendsto (fun m => ENNReal.ofReal t⁻¹ * n1 C la (F m)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hn1 (Or.inr ENNReal.ofReal_ne_top)
    simpa using (ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofNat_ne_top)).add
      (ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofNat_ne_top))

  have hG : ∀ a, ∃ g : V n → ℂ, DifferentiableOn ℂ g (ball (C.c a) (C.r a)) ∧
      g =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm := by
    intro a
    have hρ : ContinuousOn (fun v => Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
        (ball (C.c a) (C.r a)) :=
      Real.continuous_exp.comp_continuousOn
        (((A.smooth_ph la (C.idx a)).continuousOn.mono (hWsub a)).neg)
    refine GlobalTheory.T.exists_differentiableOn_ae_eq_of_weighted_L2_limit n (ball (C.c a) (C.r a)) _ (fun m => u m a)
      (f (C.idx a) ∘ (A.chart (C.idx a)).symm) isOpen_ball hρ (fun v _ => Real.exp_pos _)
      (fun m => hu m a) ((hfm (C.idx a)).mono_measure (Measure.restrict_mono (hWsub a) le_rfl)) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => bot_le) ?_
    intro m
    have hY : AEMeasurable (fun v => 2 * ENNReal.ofReal
        (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))))
        (volume.restrict (ball (C.c a) (C.r a))) := by
      refine AEMeasurable.const_mul ?_ _
      refine ContinuousOn.aemeasurable ?_ measurableSet_ball
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.mul ?_ hρ
      refine ContinuousOn.pow ?_ 2
      refine ContinuousOn.norm ?_
      exact ((((hF m).1 (C.idx a)).continuousOn.mono (hWsub a))).sub (hu m a).continuousOn
    calc ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖(f (C.idx a) ∘ (A.chart (C.idx a)).symm) v - u m a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
        ≤ ∫⁻ v in ball (C.c a) (C.r a), (2 * ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) +
          2 * ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) :=
          lintegral_mono (fun v => ofReal_sq_sub_mul_le _ _ _ _ (Real.exp_pos _).le)
      _ = 2 * (∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) +
          2 * (∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) := by
          rw [lintegral_add_right' _ hY, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      _ ≤ 2 * ENNReal.ofReal (4 * K / 4 ^ m) + 2 * (ENNReal.ofReal t⁻¹ * n1 C la (F m)) := by
          gcongr
          · exact hD m a
          · exact hule m a
  choose g hg hgae using hG
  obtain ⟨G, hGs, hGae⟩ := GlobalTheory.T.exists_holo_section_ae_eq_of_ball_cover n Y ι La A C (A.kap + la) f g hfc hg hgae
  refine ⟨G, hGs, ?_⟩
  have e : n0 A la (F 0 - G) = n0 A la (F 0 - f) := by
    unfold n0
    apply lintegral_congr_ae
    filter_upwards [hGae] with y hy
    simp only [WeightedAtlas.nsq, Pi.sub_apply, hy]
  rw [e]
  simpa using hfn 0

end GlobalTheory.OTY
