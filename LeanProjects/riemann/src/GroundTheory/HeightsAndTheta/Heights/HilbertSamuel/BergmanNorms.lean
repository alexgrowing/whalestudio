import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

theorem continuousOn_source_of_chart {E : Type*} [TopologicalSpace E] {f : X → E} (j : Fin A.n)
    (hf : ContinuousOn (f ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source)) :
    ContinuousOn f (A.chart j).source := by
  have h := hf.comp (A.chart j).continuousOn (fun y hy =>
    ⟨(A.chart j).map_source hy, by simpa [(A.chart j).left_inv hy] using hy⟩)
  exact h.congr (fun y hy => by simp [(A.chart j).left_inv hy])

theorem ptNormSq_eq_of_mem (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    ptNormSq W n s x = ‖s j x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j x) := by
  have hk : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hkj : x ∈ (A.chart (chartIdx A x)).source ∩ (A.chart j).source := ⟨hk, hx⟩
  have hg : 0 < ‖L.g (chartIdx A x) j x‖ ^ 2 := by
    have := L.ne_zero _ _ x hkj
    positivity
  have he : Real.exp ((n : ℝ) * Real.log (‖L.g (chartIdx A x) j x‖ ^ 2)) =
      (‖L.g (chartIdx A x) j x‖ ^ 2) ^ n := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hg n)]
  rw [ptNormSq, hs.2.1 _ j x hkj, W.compat _ j x hkj, norm_mul, norm_pow,
    show -(n : ℝ) * (W.φ j x + Real.log (‖L.g (chartIdx A x) j x‖ ^ 2)) =
      -(n : ℝ) * W.φ j x - (n : ℝ) * Real.log (‖L.g (chartIdx A x) j x‖ ^ 2) by ring,
    Real.exp_sub, he]
  have hp : 0 < (‖L.g (chartIdx A x) j x‖ ^ 2) ^ n := pow_pos hg n
  field_simp
  ring

theorem ptNormSq_nonneg (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    0 ≤ ptNormSq W n s x := by
  unfold ptNormSq; positivity

theorem continuous_ptNormSq (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) : Continuous (ptNormSq W n s) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hx⟩ := A.cover x
  have hsj : ContinuousOn (s j) (A.chart j).source :=
    continuousOn_source_of_chart j (hs.1 j j).continuousOn
  have hφj : ContinuousOn (W.φ j) (A.chart j).source :=
    continuousOn_source_of_chart j (W.smooth j j).continuousOn
  have hF : ContinuousOn (fun y => ‖s j y‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j y))
      (A.chart j).source :=
    ((hsj.norm.pow 2).mul ((continuousOn_const.mul hφj).rexp))
  have hopen := (A.chart j).open_source
  refine (hF.continuousAt (hopen.mem_nhds hx)).congr ?_
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact (ptNormSq_eq_of_mem W hs j hy).symm

theorem ptNormSq_smul (W : Weight L) (n : ℕ) (c : ℂ) (s : Fin A.n → X → ℂ) (x : X) :
    ptNormSq W n (c • s) x = ‖c‖ ^ 2 * ptNormSq W n s x := by
  simp only [ptNormSq, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

variable [MeasurableSpace X] [BorelSpace X]

theorem SmoothVolume.isOpenPosMeasure (dV : SmoothVolume A) : dV.μ.IsOpenPosMeasure := by
  refine ⟨fun U hU ⟨x, hxU⟩ hzero => ?_⟩
  obtain ⟨j, hx⟩ := A.cover x
  set O := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U with hOdef
  have hO : IsOpen O := (A.chart j).isOpen_inter_preimage_symm hU
  have hxO : A.chart j x ∈ O :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hxU⟩
  have hOt : O ⊆ (A.chart j).target := inter_subset_left
  have hmeas : Measurable (U.indicator (1 : X → ℝ≥0∞)) := measurable_one.indicator hU.measurableSet
  have h1 := dV.chart_lintegral j _ hmeas
  have hL : ∫⁻ y in (A.chart j).source, U.indicator (1 : X → ℝ≥0∞) y ∂dV.μ = 0 := by
    rw [lintegral_indicator_one hU.measurableSet, Measure.restrict_apply hU.measurableSet]
    exact measure_mono_null inter_subset_left hzero
  rw [hL] at h1
  have h2 : ∫⁻ y in O, ENNReal.ofReal (dV.dens j y) = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ y in O, ENNReal.ofReal (dV.dens j y)
        = ∫⁻ y in O, U.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) *
            ENNReal.ofReal (dV.dens j y) := by
          refine setLIntegral_congr_fun hO.measurableSet fun y hy => ?_
          rw [Set.indicator_of_mem (show (A.chart j).symm y ∈ U from hy.2), Pi.one_apply, one_mul]
      _ ≤ ∫⁻ y in (A.chart j).target, U.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) *
            ENNReal.ofReal (dV.dens j y) := lintegral_mono_set hOt
      _ = 0 := h1.symm
  have hae : AEMeasurable (fun y => ENNReal.ofReal (dV.dens j y)) (volume.restrict O) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((((dV.smooth j).continuousOn).mono hOt).aemeasurable hO.measurableSet)
  have h3 := (lintegral_eq_zero_iff' hae).1 h2
  rw [EventuallyEq, ae_restrict_iff' hO.measurableSet] at h3
  have h4 : volume O = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h3] with y hy hyO
    exact (ENNReal.ofReal_pos.2 (dV.pos j y (hOt hyO))).ne' (hy hyO)
  exact hO.measure_ne_zero volume ⟨_, hxO⟩ h4

theorem integrable_ptNormSq (W : Weight L) (dV : SmoothVolume A) [CompactSpace X] {n : ℕ}
    {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) : Integrable (ptNormSq W n s) dV.μ := by
  have := dV.isProb
  exact (continuous_ptNormSq W hs).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [BorelSpace X] in
theorem sectionL2NormSq_nonneg (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) :
    0 ≤ sectionL2NormSq W dV n s :=
  integral_nonneg fun x => ptNormSq_nonneg W n s x

omit [BorelSpace X] in

theorem sectionL2NormSq_smul (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (c : ℂ)
    (s : Fin A.n → X → ℂ) : sectionL2NormSq W dV n (c • s) = ‖c‖ ^ 2 * sectionL2NormSq W dV n s := by
  simp only [sectionL2NormSq, ptNormSq_smul]
  exact integral_const_mul _ _

theorem ptNormSq_eq_zero_of_l2NormSq_eq_zero (W : Weight L) (dV : SmoothVolume A) [CompactSpace X]
    {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) (h0 : sectionL2NormSq W dV n s = 0) (x : X) :
    ptNormSq W n s x = 0 := by
  have := dV.isOpenPosMeasure
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => ptNormSq_nonneg W n s y)
    (integrable_ptNormSq W dV hs)).1 h0
  have := (Continuous.ae_eq_iff_eq (μ := dV.μ) (continuous_ptNormSq W hs) continuous_const).1 hae
  exact congrFun this x

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
