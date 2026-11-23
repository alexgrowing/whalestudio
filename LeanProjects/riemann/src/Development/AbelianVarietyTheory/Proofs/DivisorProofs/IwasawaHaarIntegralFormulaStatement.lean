import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaHaarIntegralFormula
import Mathlib
open MeasureTheory
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_haar_integral_formula : ∀ (G Kt : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [Group Kt] [TopologicalSpace Kt]
    [IsTopologicalGroup Kt] [CompactSpace Kt] [T2Space Kt] [MeasurableSpace Kt] [BorelSpace Kt]
    (ι : Kt →* G) (P : Subgroup G) (μG : Measure G) (μP : Measure P) (μK : Measure Kt) (δ : P → ℝ≥0),
    Continuous ι → Function.Injective ι → IsClosed (P : Set G) → μG.IsHaarMeasure → μP.IsHaarMeasure →
    μK.IsHaarMeasure → (∀ h : G, μG.map (· * h) = μG) → (∀ p : P, μP.map (· * p) = δ p • μP) →
    (∀ g : G, ∃ p ∈ P, ∃ k : Kt, g = p * ι k) → ∀ Ψ : G → ℂ,
    (∀ g : G, Integrable (fun k => Ψ (ι k * g)) μK) → (∀ (p : P) (g : G), Ψ (p * g) = (δ p : ℂ) * Ψ g) →
    ∀ g : G, ∫ k, Ψ (ι k * g) ∂μK = ∫ k, Ψ (ι k) ∂μK := by
  first | exact @GlobalTheory.IwasawaAbs.kIntegral_mul_right_eq | exact GlobalTheory.IwasawaAbs.kIntegral_mul_right_eq | (intros; apply GlobalTheory.IwasawaAbs.kIntegral_mul_right_eq <;> assumption)
