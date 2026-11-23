import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeDeepWeightMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

noncomputable section

theorem measurable_poincareDeepWeight' : Measurable poincareDeepWeight := by
  have hn : Measurable fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2).measurable
  exact Measurable.ite (measurableSet_lt hn.log measurable_const) (hn.mul (hn.log.pow_const 2)).inv
    measurable_const

theorem integrableOn_inv_log_sq_mul :
    IntegrableOn (fun r : ℝ => ((Real.log r) ^ 2 * r)⁻¹) (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))) := by
  have hρ1 : Real.exp (-(Real.exp 1 / 2)) < 1 :=
    Real.exp_lt_one_iff.2 (by have := Real.exp_pos 1; linarith)
  have hcont0 : ContinuousAt (fun r : ℝ => -(Real.log r)⁻¹) 0 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    simpa using (Real.tendsto_log_nhdsNE_zero.inv_tendsto_atBot).neg
  refine intervalIntegral.integrableOn_deriv_of_nonneg (g := fun r : ℝ => -(Real.log r)⁻¹) ?_ ?_ ?_
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      exact hcont0.continuousWithinAt
    · have hl : Real.log x ≠ 0 := (Real.log_neg h (hx.2.trans_lt hρ1)).ne
      exact ((Real.continuousAt_log h.ne').inv₀ hl).neg.continuousWithinAt
  · intro x hx
    have hl : Real.log x ≠ 0 := (Real.log_neg hx.1 (hx.2.trans hρ1)).ne
    have hx0 : x ≠ 0 := hx.1.ne'
    have : HasDerivAt (fun r : ℝ => -(Real.log r)⁻¹) (-(-x⁻¹ / Real.log x ^ 2)) x :=
      ((Real.hasDerivAt_log hx0).inv hl).neg
    refine this.congr_deriv ?_
    rw [neg_div, neg_neg]
    ring
  · intro x hx
    exact inv_nonneg.2 (mul_nonneg (sq_nonneg _) hx.1.le)

theorem ofReal_mul_poincareDeepWeight_le (r : ℝ) :
    ENNReal.ofReal r * ENNReal.ofReal (if Real.log (|r| ^ 2) < -Real.exp 1 then
        (|r| ^ 2 * Real.log (|r| ^ 2) ^ 2)⁻¹ else 0) ≤
      (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))).indicator
        (fun r : ℝ => ENNReal.ofReal (((Real.log r) ^ 2 * r)⁻¹ / 4)) r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ENNReal.ofReal_of_nonpos hr]
  · rw [abs_of_pos hr]
    split_ifs with hc
    · have hl : Real.log (r ^ 2) = 2 * Real.log r := by rw [Real.log_pow]; norm_num
      rw [hl] at hc
      have hlr : Real.log r < -(Real.exp 1 / 2) := by linarith
      have hl0 : Real.log r ≠ 0 := (hlr.trans (by have := Real.exp_pos 1; linarith)).ne
      rw [Set.indicator_of_mem (show r ∈ Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2))) from ⟨hr, ((Real.log_lt_iff_lt_exp hr).1 hlr).le⟩), ← ENNReal.ofReal_mul hr.le, hl]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      field_simp
      ring
    · simp

theorem lintegral_poincareDeepWeight_lt_top :
    ∫⁻ z : ℂ, ENNReal.ofReal (poincareDeepWeight z) < ⊤ := by
  set ρ := Real.exp (-(Real.exp 1 / 2))
  set h : ℝ → ENNReal := (Set.Ioc 0 ρ).indicator
    (fun r : ℝ => ENNReal.ofReal (((Real.log r) ^ 2 * r)⁻¹ / 4)) with hh
  have hm : Measurable h := by
    refine Measurable.indicator ?_ measurableSet_Ioc
    exact ENNReal.measurable_ofReal.comp
      (((Real.measurable_log.pow_const 2).mul measurable_id).inv.div_const 4)
  rw [← Complex.lintegral_comp_polarCoord_symm]
  calc ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ENNReal.ofReal (poincareDeepWeight (Complex.polarCoord.symm p))
      ≤ ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, h p.1 * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
        rw [polarCoord_target]
        refine lintegral_mono fun p => ?_
        simp only [poincareDeepWeight, Complex.norm_polarCoord_symm, smul_eq_mul, mul_one, hh]
        exact ofReal_mul_poincareDeepWeight_le p.1
    _ = (∫⁻ r in Set.Ioi 0, h r) * ∫⁻ _ in Set.Ioo (-Real.pi) Real.pi, 1 := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_mul hm.aemeasurable aemeasurable_const
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ?_ ?_
        · refine (setLIntegral_le_lintegral _ _).trans_lt ?_
          rw [hh, lintegral_indicator measurableSet_Ioc]
          exact ((integrableOn_inv_log_sq_mul).div_const 4).lintegral_lt_top
        · rw [setLIntegral_one, Real.volume_Ioo]
          exact ENNReal.ofReal_lt_top

theorem TubeDeepWeightMass.proof : TubeDeepWeightMass.Statement := by
  intro d R
  set T : Set (Fin d → ℂ) := {w | ∀ i, ‖w i‖ ≤ R} with hTdef
  have hT : volume T < ⊤ := by
    have hsub : T ⊆ Metric.closedBall (0 : Fin d → ℂ) |R| := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 fun i => (hw i).trans (le_abs_self R)
    exact (measure_mono hsub).trans_lt measure_closedBall_lt_top
  have e := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0
  have hpre : {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R} =
      MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0 ⁻¹' (Set.univ ×ˢ T) := by
    ext z
    simp [hTdef, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.tail]
  have key := e.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun p : ℂ × (Fin d → ℂ) => ENNReal.ofReal (poincareDeepWeight p.1) * (fun _ => (1 : ENNReal)) p.2)
    (Set.univ ×ˢ T)
  rw [hpre]
  simp only [mul_one] at key
  have h0 : ∀ z : Fin (d + 1) → ℂ, (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0 z).1 = z 0 := fun z => rfl
  simp only [h0] at key
  rw [key, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have := lintegral_prod_mul (μ := (volume : Measure ℂ).restrict Set.univ)
    (ν := (volume : Measure (Fin d → ℂ)).restrict T)
    (ENNReal.measurable_ofReal.comp measurable_poincareDeepWeight').aemeasurable
    (aemeasurable_const (b := (1 : ENNReal)))
  simp only [mul_one, Function.comp_apply] at this
  rw [this, Measure.restrict_univ, setLIntegral_one]
  exact ENNReal.mul_lt_top lintegral_poincareDeepWeight_lt_top hT

end

end GroundTheory.Heights₂.Heights
