import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem lintegral_nsq_chart_part : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (i : ι) (W : Set (V n)) (D : ι → Y → ℂ), MeasurableSet W → W ⊆ (A.chart i).target → (∀ y ∈ (A.chart i).source, A.chart i y ∈ W → D (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D i y) → AEMeasurable (D i ∘ (A.chart i).symm) (volume.restrict W) → ∫⁻ y in (A.chart i).source ∩ A.chart i ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu = ∫⁻ v in W, ENNReal.ofReal (‖D i ((A.chart i).symm v)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A la i W D hW hWt hD hae
  classical
  set e := A.chart i with he
  have hS : MeasurableSet e.source := e.open_source.measurableSet
  have hT : MeasurableSet e.target := e.open_target.measurableSet

  set c : Y → V n := e.source.piecewise e (fun _ => 0) with hc
  have hcm : Measurable c :=
    ContinuousOn.measurable_piecewise e.continuousOn continuousOn_const hS
  set P : V n → ℝ := e.target.piecewise (fun v => A.ph (A.kap + la) i (e.symm v)) (fun _ => 0) with hP
  have hPm : Measurable P :=
    ContinuousOn.measurable_piecewise (A.smooth_ph (A.kap + la) i).continuousOn continuousOn_const hT
  set D' : V n → ℂ := hae.mk _ with hD'
  have hD'm : Measurable D' := hae.measurable_mk
  have hDD' : (D i ∘ e.symm) =ᵐ[volume.restrict W] D' := hae.ae_eq_mk
  have hcs : ∀ y ∈ e.source, c y = e y := fun y hy => by simp [hc, hy]
  have hPt : ∀ v ∈ e.target, P v = A.ph (A.kap + la) i (e.symm v) := fun v hv => by simp [hP, hv]
  set S : Set Y := e.source ∩ c ⁻¹' W with hSdef
  have hSm : MeasurableSet S := hS.inter (hcm hW)
  have hSeq : e.source ∩ e ⁻¹' W = S := by
    ext y; constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [hcs y h1] using h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [hcs y h1] using h2⟩
  set G : Y → ℝ≥0∞ := S.indicator (fun y => ENNReal.ofReal (‖D' (c y)‖ ^ 2 * Real.exp (-P (c y))))
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hSm
    exact ENNReal.measurable_ofReal.comp
      (((hD'm.comp hcm).norm.pow_const 2).mul ((hPm.comp hcm).neg.exp))

  set T : Set (V n) := toMeasurable (volume.restrict W) {v | ¬ (D i ∘ e.symm) v = D' v}
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT0 : volume.restrict W T = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp hDD'
  set E : Set Y := e.source ∩ c ⁻¹' (T ∩ W)
  have hEm : MeasurableSet E := hS.inter (hcm (hTm.inter hW))
  have hE0 : A.mu E = 0 := by
    rw [A.mu_chart i E hEm Set.inter_subset_left]
    apply setLIntegral_measure_zero
    refine measure_mono_null ?_ (show volume (T ∩ W) = 0 by
      rwa [Measure.restrict_apply hTm] at hT0)
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    simpa [hcs y hy1] using hy2

  have hL : ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu =
      ∫⁻ y in e.source, G y ∂A.mu := by
    rw [hSeq]
    have h1 : ∫⁻ y in S, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu =
        ∫⁻ y in e.source, S.indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) D y)) y ∂A.mu := by
      rw [lintegral_indicator hSm, Measure.restrict_restrict hSm,
        Set.inter_eq_left.mpr Set.inter_subset_left]
    rw [h1]
    apply lintegral_congr_ae
    have hnE : ∀ᵐ y ∂A.mu, y ∉ E := measure_eq_zero_iff_ae_notMem.mp hE0
    filter_upwards [ae_restrict_of_ae hnE, ae_restrict_mem hS] with y hyE hys
    by_cases hyS : y ∈ S
    · simp only [G, Set.indicator_of_mem hyS]
      congr 1
      have hyW : e y ∈ W := by simpa [hcs y hys] using hyS.2
      have hyT : e y ∉ T := fun h => hyE ⟨hys, by simp [hcs y hys, h, hyW]⟩
      have hDy : D i y = D' (c y) := by
        rw [hcs y hys]
        have : (D i ∘ e.symm) (e y) = D' (e y) := by
          by_contra hne
          exact hyT (subset_toMeasurable _ _ hne)
        simpa [e.left_inv hys] using this
      have hPy : P (c y) = A.ph (A.kap + la) i y := by
        rw [hcs y hys, hPt _ (e.map_source hys), e.left_inv hys]
      rw [← hDy, hPy]

      unfold WeightedAtlas.nsq
      have hp := A.mem_pick y
      have hg := A.g_ne (A.kap + la) (A.pick y) i y hp hys
      have hg2 : 0 < ‖A.g (A.kap + la) (A.pick y) i y‖ ^ 2 := by positivity
      have ht := A.ph_trans (A.kap + la) (A.pick y) i y hp hys
      rw [hD y hys hyW, norm_mul, mul_pow]
      have : A.ph (A.kap + la) (A.pick y) y =
          A.ph (A.kap + la) i y + Real.log (‖A.g (A.kap + la) (A.pick y) i y‖ ^ 2) := by linarith
      rw [this, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hg2]
      field_simp
    · simp [G, Set.indicator_of_notMem hyS]

  rw [hL, ap_lintegral_chart A i G hGm]
  have h2 : ∫⁻ v in e.target, G (e.symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v))) =
      ∫⁻ v in e.target, W.indicator (fun v => ENNReal.ofReal (‖D' v‖ ^ 2 * Real.exp (-P v)) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v)))) v := by
    refine setLIntegral_congr_fun hT fun v hv => ?_
    have hs := e.map_target hv
    have hcv : c (e.symm v) = v := by rw [hcs _ hs, e.right_inv hv]
    by_cases hvW : v ∈ W
    · have : e.symm v ∈ S := ⟨hs, by simpa [hcv] using hvW⟩
      simp only [G, Set.indicator_of_mem this, Set.indicator_of_mem hvW, hcv]
    · have : e.symm v ∉ S := fun h => hvW (by simpa [hcv] using h.2)
      simp [G, Set.indicator_of_notMem this, Set.indicator_of_notMem hvW]
  rw [h2, lintegral_indicator hW, Measure.restrict_restrict hW, Set.inter_eq_left.mpr hWt]
  apply lintegral_congr_ae
  filter_upwards [hDD', ae_restrict_mem hW] with v hv hvW
  have hvt := hWt hvW
  have hs := e.map_target hvt
  simp only [Function.comp_apply] at hv
  rw [← hv, hPt v hvt, A.ph_add A.kap la i _ hs, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [neg_add, Real.exp_add]
  have := Real.exp_pos (A.ph A.kap i (e.symm v))
  rw [Real.exp_neg (A.ph A.kap i _)]
  field_simp

end GlobalTheory.OTY
