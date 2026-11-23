import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.TwEst.quot_holo_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), ∀ (la : La) (U Ω : Set Y) (β h : ι → Y → ℂ), IsOpen U → IsOpen Ω →
    A.IsFrameOn la U β → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) →
    (∀ i, DifferentiableOn ℂ (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) ∧
    Measurable (_root_.GlobalTheory.OTY.TwEst.ext0 U (fun y : U => _root_.GlobalTheory.OTY.TwEst.quot A h β y)) ∧
    ∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * _root_.GlobalTheory.OTY.TwEst.quot A h β y := by
  intro n Y _ _ _ _ _ ι La _ A la U Ω β h hU hΩ hβ hh h0
  classical
  obtain ⟨⟨hβhol, hβcoc⟩, hβne⟩ := hβ
  obtain ⟨hhhol, hhcoc⟩ := hh
  have hq : ∀ y, _root_.GlobalTheory.OTY.TwEst.quot A h β y = h (A.pick y) y / β (A.pick y) y := fun y => by
    unfold _root_.GlobalTheory.OTY.TwEst.quot; rfl
  have hβi : ∀ i, ∀ y ∈ (A.chart i).source, y ∈ U → β i y ≠ 0 := by
    intro i y hy hyU hzero
    apply hβne y hyU
    rw [hβcoc (A.pick y) i y hyU (A.mem_pick y) hy, hzero, mul_zero]
  have hqe : ∀ i, ∀ y ∈ (A.chart i).source, y ∈ U →
      _root_.GlobalTheory.OTY.TwEst.quot A h β y = h i y / β i y := by
    intro i y hy hyU
    rw [hq]
    by_cases hyΩ : y ∈ Ω
    · rw [hhcoc (A.pick y) i y hyΩ (A.mem_pick y) hy, hβcoc (A.pick y) i y hyU (A.mem_pick y) hy,
        mul_div_mul_left _ _ (A.g_ne la _ _ y (A.mem_pick y) hy)]
    · rw [h0 _ _ hyΩ, h0 _ _ hyΩ, zero_div, zero_div]
  have hdiff : ∀ i, DifferentiableOn ℂ (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω)) := by
    intro i
    set S := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) with hS
    have h1 : DifferentiableOn ℂ (h i ∘ (A.chart i).symm) S :=
      (hhhol i).mono fun v hv => ⟨hv.1, hv.2.2⟩
    have h2 : DifferentiableOn ℂ (β i ∘ (A.chart i).symm) S :=
      (hβhol i).mono fun v hv => ⟨hv.1, hv.2.1⟩
    have h3 : ∀ v ∈ S, (β i ∘ (A.chart i).symm) v ≠ 0 := fun v hv =>
      hβi i _ ((A.chart i).map_target hv.1) hv.2.1
    have hd : DifferentiableOn ℂ
        (fun v => (h i ∘ (A.chart i).symm) v * ((β i ∘ (A.chart i).symm) v)⁻¹) S :=
      h1.mul (h2.inv h3)
    refine hd.congr fun v hv => ?_
    simp only [Function.comp_apply, ← div_eq_mul_inv]
    exact hqe i _ ((A.chart i).map_target hv.1) hv.2.1
  refine ⟨hdiff, ?_, fun y hy => ?_⟩
  · have hopen : IsOpen (U ∩ Ω) := hU.inter hΩ
    have hcont : ContinuousOn (_root_.GlobalTheory.OTY.TwEst.quot A h β) (U ∩ Ω) := by
      intro y hy
      set i := A.pick y
      have hys : y ∈ (A.chart i).source := A.mem_pick y
      have hset : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω)) :=
        (A.chart i).isOpen_inter_preimage_symm hopen
      have hmem : A.chart i y ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) :=
        ⟨(A.chart i).map_source hys, by
          simp only [Set.mem_preimage, (A.chart i).left_inv hys]; exact hy⟩
      have hca : ContinuousAt (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) (A.chart i y) :=
        ((hdiff i).continuousOn).continuousAt (hset.mem_nhds hmem)
      have hcomp : ContinuousAt ((_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) ∘ A.chart i) y :=
        hca.comp ((A.chart i).continuousAt hys)
      refine (hcomp.congr ?_).continuousWithinAt
      filter_upwards [(A.chart i).open_source.mem_nhds hys] with w hw
      simp [(A.chart i).left_inv hw]
    have heq : _root_.GlobalTheory.OTY.TwEst.ext0 U (fun y : U => _root_.GlobalTheory.OTY.TwEst.quot A h β y) =
        (U ∩ Ω).piecewise (_root_.GlobalTheory.OTY.TwEst.quot A h β) 0 := by
      funext y
      unfold _root_.GlobalTheory.OTY.TwEst.ext0
      by_cases hyU : y ∈ U
      · by_cases hyΩ : y ∈ Ω
        · simp [hyU, hyΩ, Set.piecewise]
        · simp [hyU, hyΩ, Set.piecewise, hq, h0 _ _ hyΩ]
      · simp [hyU, Set.piecewise]
    rw [heq]
    exact hcont.measurable_piecewise continuousOn_const hopen.measurableSet
  · rw [hq, mul_div_cancel₀ _ (hβne y hy)]
