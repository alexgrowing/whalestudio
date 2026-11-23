import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem isSSec_finset_sum_and_n1_le_card_mul_sum (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    (C : Cover A) (la : La) (T : Finset Y) (F : Y → ι → Y → ℂ)
    (hF : ∀ P ∈ T, A.IsSSec (A.kap + la) (F P)) :
    A.IsSSec (A.kap + la) (fun i y => ∑ P ∈ T, F P i y) ∧
      n1 C la (fun i y => ∑ P ∈ T, F P i y) ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, n1 C la (F P) := by
  refine ⟨⟨fun i => ?_, fun i j y hi hj => ?_⟩, ?_⟩
  · exact ContDiffOn.sum (fun P hP => (hF P hP).1 i)
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun P hP => (hF P hP).2 i j y hi hj)
  ·
    have key : ∀ a : Fin C.m,
        (∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j ((fun y => ∑ P ∈ T, F P (C.idx a) y) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))))
        ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
      intro a
      set i := C.idx a with hi
      set e := A.chart i with he
      have hball : Metric.ball (C.c a) (C.r a) ⊆ e.target :=
        Metric.ball_subset_closedBall.trans (C.sub a)
      have hdiff : ∀ P ∈ T, ∀ v ∈ Metric.ball (C.c a) (C.r a),
          DifferentiableAt ℝ (F P i ∘ e.symm) v := fun P hP v hv =>
        ((hF P hP).1 i).differentiableOn (by simp) |>.differentiableAt
          (e.open_target.mem_nhds (hball hv))

      have hcont : ∀ P ∈ T, ContinuousOn (fun v => ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) *
            Real.exp (-A.ph la i (e.symm v)))) (Metric.ball (C.c a) (C.r a)) := by
        intro P hP
        have hfd : ContinuousOn (fderiv ℝ (F P i ∘ e.symm)) e.target :=
          ((hF P hP).1 i).continuousOn_fderiv_of_isOpen e.open_target (by simp)
        have hph : ContinuousOn (fun v => A.ph la i (e.symm v)) e.target :=
          (A.smooth_ph la i).continuousOn
        refine ENNReal.continuous_ofReal.comp_continuousOn ?_
        refine ContinuousOn.mul ?_ ((hph.mono hball).neg.rexp)
        refine continuousOn_finset_sum _ (fun j _ => ?_)
        refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
        unfold wdb
        refine ContinuousOn.div_const (ContinuousOn.add ?_ (continuousOn_const.mul ?_)) _
        · exact (hfd.clm_apply continuousOn_const).mono hball
        · exact (hfd.clm_apply continuousOn_const).mono hball
      have hpt : ∀ v ∈ Metric.ball (C.c a) (C.r a),
          ENNReal.ofReal ((∑ j, ‖wdb n j ((fun y => ∑ P ∈ T, F P i y) ∘ e.symm) v‖ ^ 2) *
            Real.exp (-A.ph la i (e.symm v)))
          ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, ENNReal.ofReal
            ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))) := by
        intro v hv
        have hfun : (fun y => ∑ P ∈ T, F P i y) ∘ e.symm = fun w => ∑ P ∈ T, (F P i ∘ e.symm) w := rfl
        rw [hfun]
        have hs : ∀ j, wdb n j (fun w => ∑ P ∈ T, (F P i ∘ e.symm) w) v
            = ∑ P ∈ T, wdb n j (F P i ∘ e.symm) v := fun j => wdb_sum T (fun P hP => hdiff P hP v hv)
        simp only [hs]
        have hE := Real.exp_pos (-A.ph la i (e.symm v))
        have hreal : (∑ j, ‖∑ P ∈ T, wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))
            ≤ (T.card : ℝ) * ∑ P ∈ T, (∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) *
              Real.exp (-A.ph la i (e.symm v)) := by
          rw [← Finset.sum_mul, ← mul_assoc, Finset.sum_comm, Finset.mul_sum]
          refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) hE.le
          calc ‖∑ P ∈ T, wdb n j (F P i ∘ e.symm) v‖ ^ 2
              ≤ (∑ P ∈ T, ‖wdb n j (F P i ∘ e.symm) v‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
            _ ≤ (T.card : ℝ) * ∑ P ∈ T, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2 :=
                sq_sum_le_card_mul_sum_sq
        refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun P _ => by positivity)]
      calc _ ≤ ∫⁻ v in Metric.ball (C.c a) (C.r a), (T.card : ℝ≥0∞) * ∑ P ∈ T, ENNReal.ofReal
            ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))) :=
            lintegral_mono_ae ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).2
              (Filter.Eventually.of_forall hpt))
        _ = _ := by
          rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
            lintegral_finset_sum' _ (fun P hP => (hcont P hP).aemeasurable
              Metric.isOpen_ball.measurableSet)]
    unfold n1
    calc _ ≤ ∑ a, (T.card : ℝ≥0∞) * ∑ P ∈ T, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) :=
          Finset.sum_le_sum fun a _ => key a
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end GlobalTheory.OTY
