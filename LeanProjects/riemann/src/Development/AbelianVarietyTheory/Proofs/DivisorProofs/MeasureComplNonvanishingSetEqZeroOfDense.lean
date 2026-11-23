import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem zeroSet_null_of_dense_nz : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.mu (nz A τ)ᶜ = 0 := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ hτ hd
  have hN : EXTNullStatement n := extNull n
  have hiff : ∀ i y, y ∈ (A.chart i).source → (τ (A.pick y) y ≠ 0 ↔ τ i y ≠ 0) := by
    intro i y hy
    rw [hτ.2 (A.pick y) i y trivial (A.mem_pick y) hy]
    simp [A.g_ne Λ (A.pick y) i y (A.mem_pick y) hy]
  refine measure_null_of_locally_null _ fun y _ => ?_
  have hys : y ∈ (A.chart (A.pick y)).source := A.mem_pick y
  have hv := (A.chart (A.pick y)).map_source hys
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 (A.chart (A.pick y)).open_target _ hv
  have hUo : IsOpen ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) :=
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
  have hyU : y ∈ (A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r := ⟨hys, Metric.mem_ball_self hr⟩
  have hF : DifferentiableOn ℂ (τ (A.pick y) ∘ (A.chart (A.pick y)).symm)
      (A.chart (A.pick y)).target := by
    simpa using hτ.1 (A.pick y)
  have hcont : ContinuousOn (τ (A.pick y)) (A.chart (A.pick y)).source := by
    have := hF.continuousOn.comp (A.chart (A.pick y)).continuousOn
      (fun x hx => (A.chart (A.pick y)).map_source hx)
    refine this.congr fun x hx => ?_
    simp [Function.comp, (A.chart (A.pick y)).left_inv hx]
  have hTo : IsOpen (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ) :=
    (hcont.mono Set.inter_subset_left).isOpen_inter_preimage hUo isOpen_compl_singleton
  refine ⟨_, inter_mem_nhdsWithin _ (hUo.mem_nhds hyU), ?_⟩
  refine measure_mono_null (t := ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) \ (((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
      Metric.ball (A.chart (A.pick y) y) r) ∩ τ (A.pick y) ⁻¹' {0}ᶜ)) ?_ ?_
  · rintro x ⟨hxn, hxU⟩
    refine ⟨hxU, fun h => hxn ?_⟩
    exact (hiff _ x hxU.1).2 h.2
  rw [A.mu_chart (A.pick y) _ (hUo.measurableSet.diff hTo.measurableSet)
    (Set.diff_subset.trans Set.inter_subset_left)]
  apply setLIntegral_measure_zero
  obtain ⟨y', hy'U, hy'M⟩ := hd.inter_open_nonempty _ hUo ⟨y, hyU⟩
  have hnull := hN (A.chart (A.pick y) y) r (τ (A.pick y) ∘ (A.chart (A.pick y)).symm)
    (hF.mono hB) ⟨A.chart (A.pick y) y', hy'U.2, by
      simp only [Function.comp, (A.chart _).left_inv hy'U.1]
      exact (hiff _ y' hy'U.1).1 hy'M⟩
  refine measure_mono_null ?_ hnull
  rintro _ ⟨x, ⟨hxU, hxn⟩, rfl⟩
  refine ⟨hxU.2, ?_⟩
  simp only [Set.mem_setOf_eq, Function.comp, (A.chart _).left_inv hxU.1]
  by_contra h
  exact hxn ⟨hxU, h⟩

end GlobalTheory
