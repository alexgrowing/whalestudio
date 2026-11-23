import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainUnfoldSubgroup
import Mathlib
open MeasureTheory
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_unfold_subgroup : ∀ {G G₁ : Type} [Group G] [MeasurableSpace G] [Group G₁] (N Q : Subgroup G) (Γ : Subgroup G₁)
    (μN : Measure N) (ι : G₁ → G) (𝓕 : Set N) (D : Set G) (h : G),
    Countable Q → Countable Γ → (∀ g : G, Measurable (g * ·)) →
    Measurable (fun n : N => n.1 * h) → MeasurableSet D →
    (∀ γ ∈ Γ, ι γ ∈ Q) → (∀ q ∈ Q, ∃! γ : Γ, (ι γ)⁻¹ * q ∈ N) →
    (∀ γ ∈ Γ, ∫⁻ n, D.indicator (1 : G → ENNReal) (n.1 * ι γ * h) ∂μN
      = ∫⁻ n, D.indicator (1 : G → ENNReal) (ι γ * n.1 * h) ∂μN) →
    μN.IsMulLeftInvariant → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μN →
    ∑' γ : Γ, ∫⁻ n, D.indicator (1 : G → ENNReal) (n.1 * ι γ * h) ∂μN
      = ∫⁻ n in 𝓕, ∑' q : Q, D.indicator (1 : G → ENNReal) (q.1 * (n.1 * h)) ∂μN := by
  first | exact @GlobalTheory.sum_integral_indicator_eq_setIntegral_count | exact GlobalTheory.sum_integral_indicator_eq_setIntegral_count | (intros; apply GlobalTheory.sum_integral_indicator_eq_setIntegral_count <;> assumption)
