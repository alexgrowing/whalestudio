import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries

open MeasureTheory PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology
open scoped InnerProductSpace ENNReal

theorem UpperTheory.V.Z.IntegralApplyAeEq.ae_integral {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (μ : Measure ℝ) [SFinite μ] (G : ℝ → L W) (hG : Integrable G μ) (g : ℝ × ℝ → W)
    (hg : AEStronglyMeasurable g (μ.prod volume)) (h : ∀ᵐ t ∂μ, ∀ᵐ x : ℝ, G t x = g (t, x)) :
    ∀ᵐ x : ℝ, (∫ t, G t ∂μ : L W) x = ∫ t, g (t, x) ∂μ := by
  have hint : ∀ s : Set ℝ, MeasurableSet s → volume s < ∞ → Integrable g (μ.prod (volume.restrict s)) := by
    intro s hs hf
    have hm : AEStronglyMeasurable g (μ.prod (volume.restrict s)) :=
      hg.mono_ac (Measure.AbsolutelyContinuous.rfl.prod Measure.absolutelyContinuous_restrict)
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hm.enorm]
    have hb : ∀ᵐ t ∂μ, ∫⁻ x in s, ‖g (t, x)‖ₑ ≤ ‖G t‖ₑ * volume s ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := by
      filter_upwards [h] with t ht
      have e : ∫⁻ x in s, ‖g (t, x)‖ₑ = eLpNorm (G t) 1 (volume.restrict s) := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        exact lintegral_congr_ae (ae_restrict_of_ae (ht.mono fun x hx => by simp only [hx]))
      rw [e]
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
        (Lp.aestronglyMeasurable (G t)).restrict).trans ?_
      rw [Measure.restrict_apply_univ, Lp.enorm_def]
      gcongr
      exact Measure.restrict_le_self
    refine (lintegral_mono_ae hb).trans_lt ?_
    rw [lintegral_mul_const'' _ hG.1.enorm]
    exact ENNReal.mul_lt_top hG.2 (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf.ne)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hf => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hf.ne)
    (fun s hs hf => (hint s hs hf).integral_prod_right) fun s hs hf => ?_
  rw [← integral_integral_swap (f := fun t x => g (t, x)) (hint s hs hf)]
  refine ext_inner_left ℂ fun w => ?_
  rw [← L2.inner_indicatorConstLp_eq_inner_setIntegral ℂ hs hf.ne, ← integral_inner hG,
    ← integral_inner (hint s hs hf).integral_prod_left]
  refine integral_congr_ae ?_
  filter_upwards [h] with t ht
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral ℂ hs hf.ne]
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae ht)
