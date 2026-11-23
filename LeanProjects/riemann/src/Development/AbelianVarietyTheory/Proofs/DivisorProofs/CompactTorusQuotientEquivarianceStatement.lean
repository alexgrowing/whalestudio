import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusQuotientEquivariance
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMeasure
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_torus_quotient_equivariance : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (T : Type) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T]
    [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (Q : Subgroup G) (κ : K →* G) (m : T →* G) (δ : T →* ℝ≥0) (μK : Measure K) (μT : Measure T) (μQ : Measure Q),
    IsClosed (Q : Set G) → Continuous κ → Topology.IsClosedEmbedding m → Continuous δ → μK.IsHaarMeasure → μT.IsHaarMeasure → μQ.IsHaarMeasure →
    ∀ β : G → ℝ≥0, Measurable β → (∀ x, ∫⁻ q : Q, (β (q * x) : ℝ≥0∞) ∂μQ = 1) →
    ∀ f : G → ℂ, Continuous f → (∀ q ∈ Q, ∀ x, f (q * x) = f x) →
    ∀ g, Integrable (fun p : K × T => f ((m p.2)⁻¹ * κ p.1 * g) * ((δ p.2 : ℝ) : ℂ)) (μK.prod μT) →
    ∫ x, ((β (x * g) : ℝ) : ℂ) * f (x * g) ∂(GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK) = ∫ k, ∫ t, f ((m t)⁻¹ * κ k * g) * ((δ t : ℝ) : ℂ) ∂μT ∂μK := by
  first | exact @GlobalTheory.ParabolicCoord.integral_weight_mul_coordMeasure | exact GlobalTheory.ParabolicCoord.integral_weight_mul_coordMeasure | (intros; apply GlobalTheory.ParabolicCoord.integral_weight_mul_coordMeasure <;> assumption)
