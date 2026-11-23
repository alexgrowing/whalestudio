import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusQuotientUnfolding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMeasure
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_torus_quotient_unfolding : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (T : Type) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T]
    [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (Q : Subgroup G) (κ : K →* G) (m : T →* G) (δ : T →* ℝ≥0) (μK : Measure K) (μT : Measure T) (μQ : Measure Q),
    IsClosed (Q : Set G) → Continuous κ → Topology.IsClosedEmbedding m → Continuous δ → μK.IsHaarMeasure → μT.IsHaarMeasure → μQ.IsHaarMeasure →
    ∀ k, (GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK).map (fun x => x * κ k) = GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK := by
  first | exact @GlobalTheory.ParabolicCoord.coordMeasure_map_mul_right | exact GlobalTheory.ParabolicCoord.coordMeasure_map_mul_right | (intros; apply GlobalTheory.ParabolicCoord.coordMeasure_map_mul_right <;> assumption)
