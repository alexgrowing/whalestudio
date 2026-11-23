import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxA

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem g_self (la : La) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) : A.g la i i y = 1 := by
  have h := A.g_cocycle la i i i y hy hy hy
  have h0 := A.g_ne la i i y hy hy
  have h2 : A.g la i i y * (A.g la i i y - 1) = 0 := by rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.1 h2 with h1 | h1
  · exact absurd h1 h0
  · exact sub_eq_zero.1 h1

theorem g_mul_g (la : La) (i j : ι) {y : Y} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : A.g la i j y * A.g la j i y = 1 := by
  rw [← A.g_cocycle la i j i y hi hj hi, A.g_self la i hi]

theorem nsq_chart (la : La) (s : ι → Y → ℂ) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source)
    (hs : s (A.pick y) y = A.g la (A.pick y) i y * s i y) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  have hp := A.mem_pick y
  unfold nsq
  rw [hs, A.ph_trans la i (A.pick y) y hy hp]
  have h1 := A.g_mul_g la (A.pick y) i hp hy
  have hgn : ‖A.g la i (A.pick y) y‖ ≠ 0 := norm_ne_zero_iff.2 (A.g_ne la i _ y hy hp)
  have hn : ‖A.g la (A.pick y) i y‖ ^ 2 * ‖A.g la i (A.pick y) y‖ ^ 2 = 1 := by
    rw [← mul_pow, ← norm_mul, h1, norm_one, one_pow]
  rw [neg_sub, Real.exp_sub, Real.exp_log (by positivity), Real.exp_neg, norm_mul, mul_pow,
    div_eq_mul_inv]
  linear_combination (‖s i y‖ ^ 2 * (Real.exp (A.ph la i y))⁻¹) * hn

theorem nsq_chart_of_isSec (la : La) (s : ι → Y → ℂ) (hs : A.IsSec la s) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) : A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) :=
  A.nsq_chart la s i hy (hs.2 _ i y (Set.mem_univ _) (A.mem_pick y) hy)

theorem sqn_chart {N : ℕ} (la : La) (w : Fin N → ι → Y → ℂ) (hw : ∀ k, A.IsSec la (w k)) (i : ι)
    {y : Y} (hy : y ∈ (A.chart i).source) :
    A.sqn la w y = (∑ k, ‖w k i y‖ ^ 2) * Real.exp (-A.ph la i y) := by
  unfold sqn
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => A.nsq_chart_of_isSec la (w k) (hw k) i hy

theorem aap_ph_zero (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) : A.ph 0 i y = 0 := by
  have h := A.ph_add 0 0 i y hy
  rw [add_zero] at h
  linarith

theorem aap_ph_nsmul (L : La) (k : ℕ) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) :
    A.ph (k • L) i y = k * A.ph L i y := by
  induction k with
  | zero => simp [A.aap_ph_zero i hy]
  | succ k ih => rw [succ_nsmul, A.ph_add _ _ i y hy, ih]; push_cast; ring

theorem ph_eq_sub_nsmul (la L : La) (k : ℕ) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) :
    A.ph la i y = A.ph (la - k • L) i y + k * A.ph L i y := by
  rw [← A.aap_ph_nsmul L k i hy, ← A.ph_add _ _ i y hy, sub_add_cancel]

theorem continuous_of_chart {E : Type*} [TopologicalSpace E] (f : Y → E)
    (hf : ∀ i, ContinuousOn (f ∘ (A.chart i).symm) (A.chart i).target) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hy := A.mem_pick y
  set φ := A.chart (A.pick y)
  have h1 : ContinuousAt (f ∘ φ.symm) (φ y) :=
    (hf _).continuousAt (φ.open_target.mem_nhds (φ.map_source hy))
  have h2 : ContinuousAt (fun x => (f ∘ φ.symm) (φ x)) y := h1.comp (φ.continuousAt hy)
  refine h2.congr ?_
  filter_upwards [φ.open_source.mem_nhds hy] with x hx
  simp [φ.left_inv hx]

theorem SmoothFn.continuous {f : Y → ℝ} (hf : A.SmoothFn f) : Continuous f :=
  A.continuous_of_chart f fun i => (hf i).continuousOn

theorem aap_lintegral_chart_le (i : ι) (f : Y → ℝ≥0∞) (hf : Measurable f) (s : Set (V n))
    (hs : s ⊆ (A.chart i).target) :
    ∫⁻ v in s, f ((A.chart i).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) ≤ ∫⁻ y, f y ∂A.mu := by
  set φ := A.chart i
  set dens : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i (φ.symm v)))
  set ν := (volume.restrict φ.target).withDensity dens
  have hsymm0 : AEMeasurable φ.symm (volume.restrict φ.target) :=
    φ.continuousOn_symm.aemeasurable φ.open_target.measurableSet
  have hsymm : AEMeasurable φ.symm ν := hsymm0.mono_ac (withDensity_absolutelyContinuous _ _)
  have hdens : AEMeasurable dens (volume.restrict φ.target) := by
    have hc : ContinuousOn dens φ.target :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)
    exact hc.aemeasurable φ.open_target.measurableSet
  have hmeas : A.mu.restrict φ.source = ν.map φ.symm := by
    ext B hB
    rw [Measure.restrict_apply hB, Measure.map_apply_of_aemeasurable hsymm hB, withDensity_apply',
      Measure.restrict_restrict' φ.open_target.measurableSet,
      A.mu_chart i _ (hB.inter φ.open_source.measurableSet) Set.inter_subset_right]
    have hset : φ '' (B ∩ φ.source) = φ.symm ⁻¹' B ∩ φ.target := by
      rw [Set.inter_comm, φ.image_source_inter_eq', Set.inter_comm]
    rw [hset]
  calc ∫⁻ v in s, f (φ.symm v) * dens v
      ≤ ∫⁻ v in φ.target, f (φ.symm v) * dens v := lintegral_mono_set hs
    _ = ∫⁻ v in φ.target, dens v * f (φ.symm v) := by simp_rw [mul_comm]
    _ = ∫⁻ v, f (φ.symm v) ∂ν := (lintegral_withDensity_eq_lintegral_mul₀ hdens
          (hf.comp_aemeasurable hsymm0)).symm
    _ = ∫⁻ y, f y ∂(ν.map φ.symm) := (lintegral_map' hf.aemeasurable hsymm).symm
    _ = ∫⁻ y in φ.source, f y ∂A.mu := by rw [hmeas]
    _ ≤ ∫⁻ y, f y ∂A.mu := setLIntegral_le_lintegral _ _

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
