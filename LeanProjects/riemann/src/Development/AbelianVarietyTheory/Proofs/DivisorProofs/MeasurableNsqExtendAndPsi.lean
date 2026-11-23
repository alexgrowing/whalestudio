import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeI

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem measurable_nsq_extend_and_psi : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (Ω : Set Y) (h : ι → Y → ℂ), IsOpen Ω → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) → Measurable (A.nsq la h) ∧ ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → Measurable (psi A L s) := by
  intro n Y _ _ _ _ _ ι La _ A la Ω h hΩ hs h0
  refine ⟨?_, fun L s hs' => ?_⟩
  · classical
    have hc := api_nsq_contOn A hΩ hs
    have hm := ContinuousOn.measurable_piecewise hc
      (continuousOn_const (c := (0 : ℝ)) (s := Ωᶜ)) hΩ.measurableSet
    convert hm using 1
    funext y
    by_cases hy : y ∈ Ω
    · simp [hy]
    · simp [hy, WeightedAtlas.nsq, h0 _ y hy]
  · have hk : ∀ k, Measurable (A.nsq L (s k)) := fun k =>
      (continuousOn_univ.mp (api_nsq_contOn A isOpen_univ (hs' k))).measurable
    have hq : Measurable (A.sqn L s) := by
      unfold WeightedAtlas.sqn
      exact Finset.measurable_sum _ fun k _ => hk k
    unfold psi
    first | exact hq.log | fun_prop | measurability

end GlobalTheory.OTY
