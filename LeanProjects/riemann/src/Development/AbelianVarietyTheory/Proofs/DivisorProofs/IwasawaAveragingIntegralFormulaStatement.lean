import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaAveragingIntegralFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureIwasawaQuotient
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_averaging_integral_formula : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (P K : Subgroup G) (μG : Measure G) (μP : Measure P) (μK : Measure K) (δ : P → ℝ≥0) (b : G → ℝ≥0∞),
    IsClosed (P : Set G) → IsCompact (K : Set G) → μG.IsHaarMeasure → μP.IsHaarMeasure → μK.IsHaarMeasure →
    (∀ h : G, μG.map (· * h) = μG) → (∀ p : P, μP.map (· * p) = δ p • μP) →
    (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) → Measurable b →
    (∀ g : G, (∫⁻ q : P, b ((q : G) * g) ∂μP) ≠ 0 ∧ (∫⁻ q : P, b ((q : G) * g) ∂μP) ≠ ∞) →
    ∀ Φ : G → ℝ≥0∞, AEMeasurable Φ μG → (∀ (p : P) (g : G), Φ ((p : G) * g) = (δ p : ℝ≥0∞) * Φ g) →
    ∀ g : G, ∫⁻ k : K, Φ ((k : G) * g) ∂μK = ∫⁻ k : K, Φ (k : G) ∂μK := by
  first | exact @GlobalTheory.IwasawaAE.lintegral_mul_right_eq_of_equivariant | exact GlobalTheory.IwasawaAE.lintegral_mul_right_eq_of_equivariant | (intros; apply GlobalTheory.IwasawaAE.lintegral_mul_right_eq_of_equivariant <;> assumption)
