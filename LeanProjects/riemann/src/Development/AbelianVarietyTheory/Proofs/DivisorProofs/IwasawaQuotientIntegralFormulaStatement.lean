import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaQuotientIntegralFormula
import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_quotient_integral_formula : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (P K : Subgroup G) (μG : Measure G) (μP : Measure P) (μK : Measure K) (δ : P → ℝ≥0) (U : G → ℝ≥0∞),
    IsClosed (P : Set G) → IsCompact (K : Set G) → μG.IsHaarMeasure → μP.IsHaarMeasure → μK.IsHaarMeasure →
    (∀ h : G, μG.map (· * h) = μG) → (∀ p : P, μP.map (· * p) = δ p • μP) →
    (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) → Measurable U → (∀ g : G, U g ≠ 0 ∧ U g ≠ ∞) →
    (∀ (p : P) (g : G), U ((p : G) * g) = (δ p : ℝ≥0∞) * U g) → (∀ p : P, (p : G) ∈ K → δ p = 1) →
    ∀ Φ : G → ℝ≥0∞, (∀ (p : P) (g : G), Φ ((p : G) * g) = (δ p : ℝ≥0∞) * Φ g) →
    AEMeasurable (fun k : K => Φ (k : G)) μK → AEMeasurable Φ μG := by
  first | exact @GlobalTheory.EquivAEMeas.aemeasurable_of_equivariant | exact GlobalTheory.EquivAEMeas.aemeasurable_of_equivariant | (intros; apply GlobalTheory.EquivAEMeas.aemeasurable_of_equivariant <;> assumption)
