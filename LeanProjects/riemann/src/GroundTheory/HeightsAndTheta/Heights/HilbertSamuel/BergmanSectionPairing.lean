import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace SectionPairing

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

def pairing (W : Weight L) (n : ℕ) (s t : Fin A.n → X → ℂ) (x : X) : ℂ :=
  conj (s (chartIdx A x) x) * t (chartIdx A x) x *
    ((Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) : ℝ) : ℂ)

theorem mem_chartIdx (x : X) : x ∈ (A.chart (chartIdx A x)).source :=
  Classical.choose_spec (A.cover x)

theorem pairing_eq (W : Weight L) (n : ℕ) {s t : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (ht : t ∈ L.sections n) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    pairing W n s t x = conj (s j x) * t j x * ((Real.exp (-(n : ℝ) * W.φ j x) : ℝ) : ℂ) := by
  have hi := mem_chartIdx (A := A) x
  set i := chartIdx A x
  have hix : x ∈ (A.chart i).source ∩ (A.chart j).source := ⟨hi, hx⟩
  have hg := L.ne_zero i j x hix
  have ha : (0 : ℝ) < ‖L.g i j x‖ ^ 2 := pow_pos (norm_pos_iff.2 hg) 2
  have hexp : Real.exp (-(n : ℝ) * (W.φ j x + Real.log (‖L.g i j x‖ ^ 2))) =
      Real.exp (-(n : ℝ) * W.φ j x) / (‖L.g i j x‖ ^ 2) ^ n := by
    rw [show -(n : ℝ) * (W.φ j x + Real.log (‖L.g i j x‖ ^ 2)) =
        -(n : ℝ) * W.φ j x - n * Real.log (‖L.g i j x‖ ^ 2) by ring, Real.exp_sub,
      Real.exp_nat_mul, Real.exp_log ha]
  have hc : conj (L.g i j x ^ n) * L.g i j x ^ n = (((‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ) := by
    rw [map_pow, ← mul_pow, Complex.conj_mul']
    push_cast
    ring
  have hne : (((‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_pos ha n).ne'
  rw [pairing, hs.2.1 i j x hix, ht.2.1 i j x hix, W.compat i j x hix, hexp]
  calc conj (L.g i j x ^ n * s j x) * (L.g i j x ^ n * t j x) *
        ((Real.exp (-(n : ℝ) * W.φ j x) / (‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ)
      = (conj (L.g i j x ^ n) * L.g i j x ^ n) *
          (conj (s j x) * t j x * ((Real.exp (-(n : ℝ) * W.φ j x) : ℝ) : ℂ)) /
          (((‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ) := by
        rw [map_mul, Complex.ofReal_div]
        ring
    _ = conj (s j x) * t j x * ((Real.exp (-(n : ℝ) * W.φ j x) : ℝ) : ℂ) := by
        rw [hc]
        field_simp

theorem pairing_self (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    pairing W n s s x = ((ptNormSq W n s x : ℝ) : ℂ) := by
  rw [pairing, ptNormSq, Complex.conj_mul']
  push_cast
  ring

theorem continuousAt_of_chart {β : Type*} [TopologicalSpace β] {f : X → β} (j : Fin A.n)
    (hf : ContinuousOn (f ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source))
    {x : X} (hx : x ∈ (A.chart j).source) : ContinuousAt f x := by
  have hy : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hx⟩
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart j).open_source
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    (hf.continuousAt (hopen.mem_nhds hy)).comp ((A.chart j).continuousAt hx)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy
  simp [(A.chart j).left_inv hy]

theorem pairing_continuous (W : Weight L) (n : ℕ) {s t : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) (ht : t ∈ L.sections n) : Continuous (pairing W n s t) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hx := mem_chartIdx (A := A) x
  set j := chartIdx A x
  have h1 : ContinuousAt (s j) x := continuousAt_of_chart j (hs.1 j j).continuousOn hx
  have h2 : ContinuousAt (t j) x := continuousAt_of_chart j (ht.1 j j).continuousOn hx
  have h3 : ContinuousAt (W.φ j) x := continuousAt_of_chart j (W.smooth j j).continuousOn hx
  have h : ContinuousAt
      (fun y ↦ conj (s j y) * t j y * ((Real.exp (-(n : ℝ) * W.φ j y) : ℝ) : ℂ)) x := by
    have h4 : ContinuousAt (fun y ↦ ((Real.exp (-(n : ℝ) * W.φ j y) : ℝ) : ℂ)) x :=
      Complex.continuous_ofReal.continuousAt.comp
        (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul h3))
    exact ((Complex.continuous_conj.continuousAt.comp h1).mul h2).mul h4
  refine h.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy
  exact (pairing_eq W n hs ht j hy).symm

theorem ptNormSq_continuous (W : Weight L) (n : ℕ) {s : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) : Continuous (ptNormSq W n s) := by
  have h := Complex.continuous_re.comp (pairing_continuous W n hs hs)
  refine h.congr fun x ↦ ?_
  simp [pairing_self]

theorem ptNormSq_nonneg (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    0 ≤ ptNormSq W n s x := by
  unfold ptNormSq
  positivity

variable [MeasurableSpace X] [BorelSpace X]

theorem isOpenPosMeasure (dV : SmoothVolume A) : dV.μ.IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 ↦ ?_⟩
  obtain ⟨x, hxU⟩ := hne
  have hx := mem_chartIdx (A := A) x
  set j := chartIdx A x
  set T := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U
  have hTo : IsOpen T := (A.chart j).isOpen_inter_preimage_symm hU
  have hTx : A.chart j x ∈ T :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hxU⟩
  have hlin := dV.chart_lintegral j (U.indicator 1) (measurable_one.indicator hU.measurableSet)
  have hleft : ∫⁻ x in (A.chart j).source, U.indicator 1 x ∂dV.μ = 0 := by
    rw [lintegral_indicator_one hU.measurableSet, Measure.restrict_apply hU.measurableSet]
    exact measure_mono_null inter_subset_left h0
  have hT : ∫⁻ y in T, ENNReal.ofReal (dV.dens j y) = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ y in T, ENNReal.ofReal (dV.dens j y)
        = ∫⁻ y in T, U.indicator 1 ((A.chart j).symm y) * ENNReal.ofReal (dV.dens j y) :=
          setLIntegral_congr_fun hTo.measurableSet fun y hy ↦ by
            rw [Set.indicator_of_mem (show (A.chart j).symm y ∈ U from hy.2), Pi.one_apply, one_mul]
      _ ≤ ∫⁻ y in (A.chart j).target,
            U.indicator 1 ((A.chart j).symm y) * ENNReal.ofReal (dV.dens j y) :=
          lintegral_mono_set inter_subset_left
      _ = 0 := by rw [← hlin, hleft]
  have hmeas : AEMeasurable (fun y ↦ ENNReal.ofReal (dV.dens j y)) (volume.restrict T) :=
    (((dV.smooth j).continuousOn.mono inter_subset_left).aemeasurable
      hTo.measurableSet).ennreal_ofReal
  have hae := (lintegral_eq_zero_iff' hmeas).1 hT
  rw [Filter.EventuallyEq, ae_restrict_iff' hTo.measurableSet] at hae
  have hzero : volume T = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with y hy hyT
    have := hy hyT
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
    exact absurd (dV.pos j y hyT.1) (not_lt.2 this)
  exact (hTo.measure_pos volume ⟨_, hTx⟩).ne' hzero

end SectionPairing

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
