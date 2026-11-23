import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientMeasureFibration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusQuotientIntegrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusQuotientInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusQuotientUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusQuotientFubiniStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusQuotientMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusQuotientEquivarianceStatement

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.ParabolicCoord

theorem quotIntegral_right_invariant : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
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
  intro G _ _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ Q κ m δ μK μT hQ hκ hm hδ hμK hμT hGuni hQuni hn hconj hinj hP hdec f hf hfQ hint g
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  let μQ : Measure Q := Measure.haar
  haveI : μQ.IsMulRightInvariant := hQuni μQ inferInstance
  obtain ⟨β, hβm, hβ1⟩ := GlobalTheory.Orb.FubiniQuot.exists_bruhat_nnreal hQ μQ
  set ν := GlobalTheory.ParabolicCoord.coordMeasure Q κ m δ μQ μT μK with hν
  haveI hc : IsFiniteMeasureOnCompacts ν :=
    GlobalTheory.T.compact_torus_quotient_fubini G K T Q κ m δ μK μT μQ hQ hκ hm hδ hμK hμT inferInstance hn hinj hP hdec
  haveI hl : ν.IsMulLeftInvariant :=
    GlobalTheory.T.compact_torus_quotient_measure G K T Q κ m hQ hκ hm hn hinj hP hdec ν hc
      (GlobalTheory.T.compact_torus_quotient_integration G K T Q κ m δ μK μT μQ hQ hκ hm hδ hμK hμT inferInstance)
      (GlobalTheory.T.compact_torus_quotient_invariance G K T Q κ m δ μK μT μQ hQ hκ hm hδ hμK hμT inferInstance hn hconj)
      (GlobalTheory.T.compact_torus_quotient_unfolding G K T Q κ m δ μK μT μQ hQ hκ hm hδ hμK hμT inferInstance)
  let μG : Measure G := Measure.haar
  haveI : μG.IsMulRightInvariant := hGuni μG inferInstance
  have hνG : ν = Measure.haarScalarFactor ν μG • μG := Measure.isMulLeftInvariant_eq_smul ν μG
  have hright : ∀ φ : G → ℂ, ∫ x, φ (x * g) ∂ν = ∫ x, φ x ∂ν := by
    intro φ
    rw [hνG, integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_mul_right_eq_self]
  have h1 : Integrable (fun p : K × T => f ((m p.2)⁻¹ * κ p.1 * 1) * ((δ p.2 : ℝ) : ℂ)) (μK.prod μT) := by
    simpa only [mul_one] using hint 1
  have eg := GlobalTheory.T.compact_torus_quotient_equivariance G K T Q κ m δ μK μT μQ hQ hκ hm hδ hμK hμT inferInstance β hβm hβ1 f hf hfQ g (hint g)
  have e1 := GlobalTheory.T.compact_torus_quotient_equivariance G K T Q κ m δ μK μT μQ hQ hκ hm hδ hμK hμT inferInstance β hβm hβ1 f hf hfQ 1 h1
  simp only [mul_one] at e1
  rw [← eg, ← e1]
  exact hright (fun x => ((β x : ℝ) : ℂ) * f x)

end GlobalTheory.ParabolicCoord
