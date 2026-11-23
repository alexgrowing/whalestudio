import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHaarMeasureNormal
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_haar_measure_normal : ∀ (G M : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
    [LocallyCompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (Q N : Subgroup G),
    IsClosed (Q : Set G) → IsClosed (N : Set G) → N ≤ Q → (∀ q ∈ Q, ∀ u ∈ N, q * u * q⁻¹ ∈ N) → ∀ m : M →* G, Continuous m →
    (∀ x, m x ∈ Q) → (∀ q ∈ Q, ∃! z : N × M, q = z.1.1 * m z.2) → ∀ (μN : Measure N) (μM : Measure M) [μN.IsHaarMeasure]
    [μM.IsHaarMeasure] (d : M → ENNReal), Continuous d → (∀ x y, d (x * y) = d x * d y) → (∀ x, d x ≠ 0 ∧ d x ≠ ⊤) →
    (∀ x (f : G → ENNReal), Measurable f → ∫⁻ u, f (m x * u.1 * (m x)⁻¹) ∂μN = d x * ∫⁻ u, f u.1 ∂μN) →
    ∃ ν : Measure Q, ν.IsHaarMeasure ∧ ∀ φ : G → ENNReal, Measurable φ → ∫⁻ q, φ q.1 ∂ν = ∫⁻ x, ∫⁻ u, φ (u.1 * m x) * d x ∂μN ∂μM := by
  first | exact @GlobalTheory.leftHaar_semidirect_coords | exact GlobalTheory.leftHaar_semidirect_coords | (intros; apply GlobalTheory.leftHaar_semidirect_coords <;> assumption)
