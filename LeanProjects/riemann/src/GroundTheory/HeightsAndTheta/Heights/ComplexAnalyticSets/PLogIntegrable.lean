import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsSheetMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarSlabMeasure
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Set Filter ComplexSets

open scoped ENNReal

noncomputable section

namespace LogIntegrableProof

variable {n : ℕ}

theorem lintegral_lt_top (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) {d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} (u : Fin n → ℂ) (R : ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hu : linForm u ∉ J) :
    ∫⁻ z in zeroSetEuc J ∩ {z | ‖z‖ ≤ R}, ‖Real.log ‖∑ j, u j * z j‖‖ₑ
      ∂(μH[((2 * d : ℕ) : ℝ)]) < ⊤ := by
  obtain ⟨C, α, hα, hC⟩ := hS n d J u R hJ hdim hu
  set S := zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | ‖z‖ ≤ R} with hSdef
  set μ := (μH[((2 * d : ℕ) : ℝ)]).restrict S
  have hsub : S ⊆ zeroSetEuc J ∩ Metric.ball 0 (R + 1) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [mem_ball_zero_iff]
    linarith [(show ‖z‖ ≤ R from hz.2)]
  have hSfin : μH[((2 * d : ℕ) : ℝ)] S < ⊤ :=
    (measure_mono hsub).trans_lt (hF n d J hJ hdim (R + 1))
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin n) => ∑ j, u j * z j := by fun_prop
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun z => Real.log ‖∑ j, u j * z j‖
  have hFm : Measurable F := Real.measurable_log.comp hcont.norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun z => max (-F z) 0
  have hGm : Measurable G := hFm.neg.max measurable_const
  set M : ℝ := max (∑ j, ‖u j‖ * R) 0

  have hFle : ∀ z ∈ S, F z ≤ M := by
    intro z hz
    refine (Real.log_le_self (norm_nonneg _)).trans ((norm_sum_le _ _).trans ?_)
    refine le_trans ?_ (le_max_left _ _)
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le z j).trans hz.2) (norm_nonneg _)

  have hG : ∫⁻ z, ENNReal.ofReal (G z) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Eventually.of_forall fun z => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro z ⟨hz, hzS⟩
      refine ⟨hzS, ?_⟩
      have htF : F z ≤ -t := by
        rcases le_max_iff.mp (show t ≤ G z from hz) with h1 | h1
        · linarith
        · linarith
      change ‖∑ j, u j * z j‖ ≤ Real.exp (-t)
      rcases (norm_nonneg (∑ j, u j * z j)).eq_or_lt with h0 | h0
      · rw [← h0]; positivity
      · exact (Real.log_le_iff_le_exp h0).mp htF
    · rw [← Real.exp_mul]; ring_nf
  have hle : ∀ z ∈ S, ‖F z‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G z) := by
    intro z hz
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hFle z hz
    rcases le_or_gt 0 (F z) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F z) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F z) 0; have := le_max_right (∑ j, ‖u j‖ * R) 0
      linarith
  refine lt_of_le_of_lt (setLIntegral_mono (g := fun z => ENNReal.ofReal M + ENNReal.ofReal (G z))
    (measurable_const.add hGm.ennreal_ofReal) hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSfin, hG⟩

end LogIntegrableProof

open LogIntegrableProof in

theorem LogIntegrable.proof (hM : SheetSumMeasurable.Statement) (hD : ChartMassCompare.Statement)
    (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) : LogIntegrable.Statement := by
  intro n d J A u φ R hJ hdim hA hu hφ
  have hcont : Continuous fun x : Fin n → ℂ => linEval u x := by unfold linEval; fun_prop
  have hwm : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖ :=
    Real.measurable_log.comp (continuous_norm.comp hcont).measurable
  refine ⟨(hM n d J A _ φ hJ hdim hA (hwm.indicator measurableSet_closedBall) hφ).2.aestronglyMeasurable,
    ?_⟩
  obtain ⟨K, hK, hDK⟩ := hD n d J A φ R hJ hdim hA hφ

  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ L * ‖WithLp.ofLp z‖ :=
    ⟨(n : ℝ) ^ (2⁻¹ : ℝ), by positivity, fun z => by
      simpa [dist_zero_right] using
        (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℂ)).dist_le_mul (WithLp.ofLp z) 0⟩
  unfold HasFiniteIntegral
  refine (hDK _ hwm).trans_lt (ENNReal.mul_lt_top hK ?_)
  refine lt_of_le_of_lt (lintegral_mono_set ?_) (lintegral_lt_top hS hF u (L * R) hJ hdim hu)
  rintro z ⟨hz, hzB⟩
  refine ⟨hz, ?_⟩
  have : ‖WithLp.ofLp z‖ ≤ R := mem_closedBall_zero_iff.mp hzB
  exact (hL z).trans (mul_le_mul_of_nonneg_left this hL0)

end

end GroundTheory.Heights₂.Heights
