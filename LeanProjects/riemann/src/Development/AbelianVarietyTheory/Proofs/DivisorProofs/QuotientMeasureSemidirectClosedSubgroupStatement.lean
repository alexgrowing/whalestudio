import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMeasureSemidirectClosedSubgroup
import Mathlib
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_measure_semidirect_closed_subgroup : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (N R : Subgroup G) (s : H →* G), IsClosed (N : Set G) → Continuous s → (∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) →
    N ⊔ s.range = R → (∃ p : R → H, Continuous p ∧ ∀ (h : H) (n : N) (hm : n.1 * s h ∈ R), p ⟨n.1 * s h, hm⟩ = h) →
    ∀ (Γ : Subgroup G) [Countable Γ] (Λ : Subgroup H) [Countable Λ], (∀ n ∈ N, ∀ h, n * s h ∈ Γ ↔ n ∈ Γ ∧ h ∈ Λ) →
    ∀ (K : Set H), IsCompact K → (∀ h, ∃ δ ∈ Λ, δ * h ∈ K) →
    ∀ (μ : Measure H) [μ.IsHaarMeasure] (𝓕 : Set H), IsFundamentalDomain Λ 𝓕 μ → μ 𝓕 = 1 →
    ∀ (ν : Measure N) [ν.IsHaarMeasure] (𝓐 : Set N), IsFundamentalDomain (Γ.subgroupOf N) 𝓐 ν → ν 𝓐 = 1 →
    ∃ (κ : Measure R) (𝓡 : Set R), κ.IsHaarMeasure ∧ IsFundamentalDomain (Γ.subgroupOf R) 𝓡 κ ∧ κ 𝓡 = 1 ∧
      ∀ φ : G → ℂ, Continuous φ → (∃ C, ∀ x ∈ R, ‖φ x‖ ≤ C) →
        ∫ x in 𝓡, φ x ∂κ = ∫ h in 𝓕, ∫ m in 𝓐, φ (m.1 * s h) ∂ν ∂μ := by
  first | exact @GlobalTheory.semiHaar_exists_fd_setIntegral | exact GlobalTheory.semiHaar_exists_fd_setIntegral | (intros; apply GlobalTheory.semiHaar_exists_fd_setIntegral <;> assumption)
