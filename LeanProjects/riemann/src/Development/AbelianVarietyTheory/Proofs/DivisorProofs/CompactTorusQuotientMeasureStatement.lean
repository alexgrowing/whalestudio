import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusQuotientMeasure
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMeasure
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_torus_quotient_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (T : Type) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T]
    [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (Q : Subgroup G) (κ : K →* G) (m : T →* G),
    IsClosed (Q : Set G) → Continuous κ → Topology.IsClosedEmbedding m →
    ∀ hn : (∀ t, ∀ q ∈ Q, (m t)⁻¹ * q * m t ∈ Q),
    (∀ t, m t ∈ Q → t = 1) →
    IsClosed {x : G | ∃ q ∈ Q, ∃ t, x = q * m t} →
    (∀ x : G, ∃ q ∈ Q, ∃ t k, x = q * (m t)⁻¹ * κ k) →
    ∀ ν : Measure G, IsFiniteMeasureOnCompacts ν → (∀ q ∈ Q, ν.map (fun x => q * x) = ν) →
    (∀ s, ν.map (fun x => m s * x) = ν) → (∀ k, ν.map (fun x => x * κ k) = ν) → ν.IsMulLeftInvariant := by
  first | exact @GlobalTheory.TwoSidedInv.isMulLeftInvariant_of_parabolic | exact GlobalTheory.TwoSidedInv.isMulLeftInvariant_of_parabolic | (intros; apply GlobalTheory.TwoSidedInv.isMulLeftInvariant_of_parabolic <;> assumption)
