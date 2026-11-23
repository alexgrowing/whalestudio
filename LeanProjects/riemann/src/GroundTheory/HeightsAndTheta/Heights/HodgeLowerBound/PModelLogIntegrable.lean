import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelPtsIntegrable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.A (coordDiv)

namespace ModelLogIntegrableAlt

theorem volume_coordDiv {D : ℕ} (S : Finset (Fin D)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  refine (measure_biUnion_null_iff S.countable_toSet).2 fun i _ => ?_
  rw [volume_pi]
  exact Measure.pi_eval_preimage_null _ (measure_singleton 0)

theorem target_inter_compl_Yo_subset {D : ℕ} {X : Type*} [TopologicalSpace X]
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X} (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (j : Fin R.N) :
    (R.chart j).target ∩ (R.chart j).symm ⁻¹' R.Yoᶜ ⊆ coordDiv (R.S j) := by
  rintro y ⟨hy, hyY⟩
  have h := R.mem_Yo j _ ((R.chart j).map_target hy)
  rw [(R.chart j).right_inv hy] at h
  by_contra hc
  exact hyY (h.2 hc)

end ModelLogIntegrableAlt

open ModelLogIntegrableAlt in

theorem ModelLogIntegrable.proof (hM : ModelPtsIntegrable.Statement) : ModelLogIntegrable.Statement := by
  intro K _ ι _ P e M R L c N u C C' g hP hL hN hu hbd hg
  let _ : MeasurableSpace M.Xc := borel M.Xc
  have _ : BorelSpace M.Xc := ⟨rfl⟩
  obtain ⟨B, hB⟩ := R.f_bdd
  refine hM K ι P e M R.N R.chart L c N R.Yoᶜ u g hP hL hN R.compat (fun x => ?_)
    (fun j => measure_mono_null (target_inter_compl_Yo_subset R j) (volume_coordDiv _))
    (fun j Q hQ hQc => ?_) (fun z hz hzN hzE => hg z hz hzN (not_not.mp hzE))
  · obtain ⟨j, hj⟩ := R.cover x
    exact ⟨j, R.toPotentialCharts.mid_subset_source j (R.toPotentialCharts.inner_subset_mid j hj)⟩

  have hQp : Q ⊆ GroundTheory.Heights₂.Heights.LogInt.polydisc (Fin e) 1 := by
    intro y hy
    have hb : ‖y‖ < 1 := by simpa using R.target_subset j (hQ hy)
    intro i _
    simpa using (norm_le_pi_norm y i).trans hb.le
  set G : (Fin e → ℂ) → ℝ := fun y => |C| + |C'| * (Real.exp 1 + B) +
    |C'| * ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| with hGdef
  have hG : IntegrableOn G Q := by
    refine IntegrableOn.mono_set ?_ hQp
    refine ((integrableOn_const (GroundTheory.Heights₂.Heights.LogInt.volume_polydisc_ne_top 1)).add
      (Integrable.const_mul (integrable_finsetSum _ fun i _ =>
        ((GroundTheory.Heights₂.Heights.LogInt.integrableOn_log_norm_coord 1 i).abs.const_mul 2)) _))
  have hmeas : AEStronglyMeasurable (fun y => u ((R.chart j).symm y)) (volume.restrict Q) :=
    (hu.comp_aemeasurable (((R.chart j).continuousOn_symm.mono hQ).aemeasurable
      hQc.isClosed.measurableSet)).aestronglyMeasurable
  refine Integrable.mono' hG hmeas ?_
  filter_upwards [ae_restrict_mem hQc.isClosed.measurableSet,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (volume_coordDiv (R.S j)))] with y hyQ hyD
  have hyt := hQ hyQ
  have hYo : (R.chart j).symm y ∈ R.Yo := by
    have h := R.mem_Yo j _ ((R.chart j).map_target hyt)
    rw [(R.chart j).right_inv hyt] at h
    exact h.2 hyD
  have h1 := hbd _ hYo
  have hr1 := R.one_le_r _ hYo
  have hrc := R.r_chart j y ⟨hyt, hyD⟩
  set r := R.r ((R.chart j).symm y) with hrdef
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlogr : Real.log r ≤ r := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < r)]
  have hf : R.f j y ≤ B := (le_abs_self _).trans (hB j y hyt)
  have hsum : ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.log_inv, Real.log_pow]
    push_cast
    linarith [neg_abs_le (Real.log ‖y i‖)]
  have hrb : r ≤ Real.exp 1 + B + ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    rw [hrc]; linarith
  have hC : C + C' * Real.log r ≤ |C| + |C'| * r := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C') hlog0
    have := mul_le_mul_of_nonneg_left hlogr (abs_nonneg C')
    linarith [le_abs_self C]
  have hC2 : |C'| * r ≤ |C'| * (Real.exp 1 + B) + |C'| * ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C')
  rw [Real.norm_eq_abs, hGdef]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
