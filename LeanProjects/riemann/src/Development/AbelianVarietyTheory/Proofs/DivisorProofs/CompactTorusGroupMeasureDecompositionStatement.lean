import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusGroupMeasureDecomposition
import Mathlib
open MeasureTheory
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_torus_group_measure_decomposition : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (T : Type) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T]
    [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (Q : Subgroup G) (κ : K →* G) (m : T →* G) (δ : T →* ℝ≥0) (μK : Measure K) (μT : Measure T),
    IsClosed (Q : Set G) → Continuous κ → Topology.IsClosedEmbedding m → Continuous δ → μK.IsHaarMeasure → μT.IsHaarMeasure →
    (∀ μ : Measure G, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
    (∀ μ : Measure Q, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
    ∀ hn : (∀ t, ∀ q ∈ Q, (m t)⁻¹ * q * m t ∈ Q),
    (∀ μ : Measure Q, μ.IsHaarMeasure → ∀ t, μ.map (fun q : Q => (⟨(m t)⁻¹ * q * m t, hn t q q.2⟩ : Q)) = δ t • μ) →
    (∀ t, m t ∈ Q → t = 1) →
    IsClosed {x : G | ∃ q ∈ Q, ∃ t, x = q * m t} →
    (∀ x : G, ∃ q ∈ Q, ∃ t k, x = q * (m t)⁻¹ * κ k) →
    ∀ f : G → ℂ, Continuous f → (∀ q ∈ Q, ∀ x, f (q * x) = f x) →
    (∀ g, Integrable (fun p : K × T => f ((m p.2)⁻¹ * κ p.1 * g) * ((δ p.2 : ℝ) : ℂ)) (μK.prod μT)) →
    ∀ g, ∫ k, ∫ t, f ((m t)⁻¹ * κ k * g) * ((δ t : ℝ) : ℂ) ∂μT ∂μK = ∫ k, ∫ t, f ((m t)⁻¹ * κ k) * ((δ t : ℝ) : ℂ) ∂μT ∂μK := by
  first | exact @GlobalTheory.ParabolicCoord.quotIntegral_right_invariant | exact GlobalTheory.ParabolicCoord.quotIntegral_right_invariant | (intros; apply GlobalTheory.ParabolicCoord.quotIntegral_right_invariant <;> assumption)
