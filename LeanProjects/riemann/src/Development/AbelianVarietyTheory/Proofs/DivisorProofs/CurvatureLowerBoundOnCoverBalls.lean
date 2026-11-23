import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtWeightAddNsmulLargeOnCompactStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.CoverCurv

theorem curv_cover : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ t : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, CurvGe C (G + k • H) t := by
  intro n Y _ _ _ _ _ ι La _ A C H G hH t
  have hk : ∀ a : Fin C.m, ∃ k0 : ℕ, ∀ k ≥ k0, ∀ v ∈ Metric.closedBall (C.c a) (C.r a),
      ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤
        A.leviAt (C.idx a) (A.ph (G + k • H) (C.idx a)) ((A.chart (C.idx a)).symm v) ξ :=
    fun a => GlobalTheory.T.leviAt_weight_add_nsmul_large_on_compact n Y ι La A H G hH (C.idx a) _ t
      (isCompact_closedBall (C.c a) (C.r a)) (C.sub a)
  choose k0 hk0 using hk
  refine ⟨Finset.univ.sup k0, fun k hk a v hv ξ => ?_⟩
  exact hk0 a k (le_trans (Finset.le_sup (Finset.mem_univ a)) hk) v
    (Metric.ball_subset_closedBall hv) ξ

end GlobalTheory.OTY.CoverCurv
