import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem contDiffAt_psi_of_notMem_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ y, y ∉ A.zeroSet s → ∀ i, y ∈ (A.chart i).source → ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i y) := by
  intro n Y _ _ _ _ _ ι La _ A L s hs y hy i hi
  have hv : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
  have hU : (A.chart i).target ∈ 𝓝 (A.chart i y) := (A.chart i).open_target.mem_nhds hv
  have hsk : ∀ k, ContDiffAt ℝ ∞ (s k i ∘ (A.chart i).symm) (A.chart i y) := fun k =>
    hyq_contDiffAt_of_holo (A.chart i).open_target (by simpa using (hs k).1 i) hv
  have hph : ContDiffAt ℝ ∞ (A.ph L i ∘ (A.chart i).symm) (A.chart i y) :=
    (A.smooth_ph L i).contDiffAt hU
  have h1 : ContDiffAt ℝ ∞ (fun v => ∑ k, ‖(s k i ∘ (A.chart i).symm) v‖ ^ 2 *
      Real.exp (-(A.ph L i ∘ (A.chart i).symm) v)) (A.chart i y) :=
    ContDiffAt.sum fun k _ => ((hsk k).norm_sq ℂ).mul hph.neg.exp
  have h2 : ContDiffAt ℝ ∞ (A.sqn L s ∘ (A.chart i).symm) (A.chart i y) := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hU] with v hv'
    simp only [Function.comp, WeightedAtlas.sqn]
    exact Finset.sum_congr rfl fun k _ =>
      WeightedAtlas.nsq_eq_chart A (hs k) ((A.chart i).map_target hv')
  have hpos : 0 < A.sqn L s y := by
    obtain ⟨k, hk⟩ : ∃ k, s k (A.pick y) y ≠ 0 := by
      by_contra h
      exact hy fun k => by_contra fun hk => h ⟨k, hk⟩
    unfold WeightedAtlas.sqn WeightedAtlas.nsq
    refine Finset.sum_pos' (fun _ _ => by positivity) ⟨k, Finset.mem_univ _, ?_⟩
    have := norm_pos_iff.2 hk
    positivity
  have h3 : (A.sqn L s ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simp only [Function.comp, (A.chart i).left_inv hi]
    exact hpos.ne'
  exact contDiffAt_const.mul (h2.log h3)

end GlobalTheory.OTY
