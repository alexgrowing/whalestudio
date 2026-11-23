import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureIwasawaQuotient
import Mathlib

open MeasureTheory Topology
open scoped NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_iwasawa_quotient : ∀ (G Λ : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [Group Λ] [TopologicalSpace Λ] [IsTopologicalGroup Λ] [LocallyCompactSpace Λ]
    [SecondCountableTopology Λ] [T2Space Λ] [MeasurableSpace Λ] [BorelSpace Λ]
    (N K : Subgroup G) (j : Λ →* G) (δ : Λ →* ℝ≥0) (μG : Measure G) (μN : Measure N) (μK : Measure K) (μΛ : Measure Λ),
    μG.IsHaarMeasure → μN.IsHaarMeasure → μK.IsHaarMeasure → μΛ.IsHaarMeasure →
    IsCompact (K : Set G) → Continuous j → Continuous δ →
    (∀ x, ∀ n ∈ N, j x * n * (j x)⁻¹ ∈ N) →
    IsClosedEmbedding (fun p : N × Λ => (p.1 : G) * j p.2) →
    (∀ x (f : G → ℝ≥0∞), Measurable f → ∫⁻ n, f (j x * n.1 * (j x)⁻¹) ∂μN = ((δ x : ℝ≥0) : ℝ≥0∞)⁻¹ * ∫⁻ n, f n.1 ∂μN) →
    (∀ g, ∃ n ∈ N, ∃ x, ∃ k ∈ K, g = n * j x * k) →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μG = c * ∫⁻ k, ∫⁻ x, ∫⁻ n, φ (n.1 * j x * k.1) * ((δ x : ℝ≥0) : ℝ≥0∞)⁻¹ ∂μN ∂μΛ ∂μK := by
  first | exact @GlobalTheory.NAK.lintegral_eq_nak | exact GlobalTheory.NAK.lintegral_eq_nak | (intros; apply GlobalTheory.NAK.lintegral_eq_nak <;> assumption)
