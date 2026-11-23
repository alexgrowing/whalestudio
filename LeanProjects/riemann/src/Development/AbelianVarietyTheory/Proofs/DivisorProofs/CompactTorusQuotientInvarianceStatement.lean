import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusQuotientInvariance
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMeasure
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_torus_quotient_invariance : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (T : Type) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T]
    [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (Q : Subgroup G) (κ : K →* G) (m : T →* G) (δ : T →* ℝ≥0) (μK : Measure K) (μT : Measure T) (μQ : Measure Q),
    IsClosed (Q : Set G) → Continuous κ → Topology.IsClosedEmbedding m → Continuous δ → μK.IsHaarMeasure → μT.IsHaarMeasure → μQ.IsHaarMeasure →
    ∀ hn : (∀ t, ∀ q ∈ Q, (m t)⁻¹ * q * m t ∈ Q),
    (∀ μ : Measure Q, μ.IsHaarMeasure → ∀ t, μ.map (fun q : Q => (⟨(m t)⁻¹ * q * m t, hn t q q.2⟩ : Q)) = δ t • μ) →
    ∀ s, (GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK).map (fun x => m s * x) = GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK := by
  first | exact @GlobalTheory.ParabolicCoord.coordMeasure_map_mul_left_m | exact GlobalTheory.ParabolicCoord.coordMeasure_map_mul_left_m | (intros; apply GlobalTheory.ParabolicCoord.coordMeasure_map_mul_left_m <;> assumption)
