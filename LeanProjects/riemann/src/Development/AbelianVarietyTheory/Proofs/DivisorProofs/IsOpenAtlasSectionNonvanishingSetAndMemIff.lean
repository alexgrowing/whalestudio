import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem isOpen_nz_and_mem_nz_iff : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → IsOpen (nz A τ) ∧ ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ h
  have key : ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
    intro i y hy
    have e := h.2 i (A.pick y) y (Set.mem_univ _) hy (A.mem_pick y)
    have g := A.g_ne Λ i (A.pick y) y hy (A.mem_pick y)
    simp only [nz, Set.mem_setOf_eq, e, ne_eq, mul_eq_zero, g, false_or]
  refine ⟨?_, key⟩
  have cont : ∀ i, ContinuousOn (τ i) (A.chart i).source := by
    intro i
    have h1 : ContinuousOn (τ i ∘ (A.chart i).symm) (A.chart i).target := by
      simpa using (h.1 i).continuousOn
    have h2 := h1.comp (A.chart i).continuousOn (A.chart i).mapsTo
    refine h2.congr ?_
    intro y hy
    simp [(A.chart i).left_inv hy]
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hs := (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousAt (τ (A.pick y)) y := (cont _).continuousAt hs
  have hne : τ (A.pick y) y ≠ 0 := hy
  filter_upwards [hs, hc.eventually_ne hne] with x hx hx'
  exact (key _ x hx).2 hx'

end GlobalTheory.OTY
