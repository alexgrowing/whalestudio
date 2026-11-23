import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem smooth_bump_chart_ball : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (i : ι) (p : V n) (ρ : ℝ), 0 < ρ → closedBall p ρ ⊆ (A.chart i).target → ∃ χ : Y → ℝ, A.SmoothFn χ ∧ tsupport χ ⊆ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball p (ρ / 2) → χ y = 1 := by
  intro n Y _ _ _ _ _ ι La _ A i p ρ hρ hK
  let b : ContDiffBump p := ⟨ρ / 2, 3 * ρ / 4, by linarith, by linarith⟩
  have hK0 : IsCompact (closedBall p (3 * ρ / 4)) := isCompact_closedBall p _
  have hK0t : closedBall p (3 * ρ / 4) ⊆ (A.chart i).target :=
    (closedBall_subset_closedBall (by linarith)).trans hK
  have hβs : ∀ u, (b : V n → ℝ) u ≠ 0 → u ∈ closedBall p (3 * ρ / 4) := by
    intro u hu
    have : u ∈ Function.support (b : V n → ℝ) := hu
    rw [b.support_eq] at this
    exact ball_subset_closedBall this
  refine ⟨A.chiC i b, A.chiC_smooth b.contDiff hβs hK0 hK0t, ?_, ?_⟩
  · have hC := (A.isCompact_chartImage hK0 hK0t).isClosed
    have hsup : Function.support (A.chiC i b) ⊆ (A.chart i).symm '' closedBall p (3 * ρ / 4) := by
      intro y hy
      by_contra h
      exact hy (A.chiC_eq_zero hβs h)
    refine (closure_minimal hsup hC).trans ?_
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨(A.chart i).map_target (hK0t hu), ?_⟩
    show A.chart i ((A.chart i).symm u) ∈ ball p ρ
    rw [(A.chart i).right_inv (hK0t hu)]
    exact closedBall_subset_ball (by linarith) hu
  · intro y hy hb
    rw [A.chiC_of_mem hy]
    exact b.one_of_mem_closedBall (ball_subset_closedBall hb)

end GlobalTheory
