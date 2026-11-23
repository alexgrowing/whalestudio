import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIndicatorTsumOne
import Mathlib
open MeasureTheory
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_indicator_tsum_one : ∀ {G : Type} [Group G] [MeasurableSpace G] (μG : Measure G) (Q : Subgroup G) (𝓓 𝓓₀ : Set G),
    Countable Q → (∀ g : G, Measurable (g * ·)) → μG.IsMulLeftInvariant →
    IsFundamentalDomain Q 𝓓 μG → MeasurableSet 𝓓₀ → 𝓓₀ ⊆ 𝓓 → μG (𝓓 \ 𝓓₀) = 0 →
    ∀ᵐ y ∂μG, ∑' q : Q, 𝓓₀.indicator (1 : G → ENNReal) ((q : G) * y) = 1 := by
  first | exact @GlobalTheory.fundamentalDomain_count_ae_eq_one | exact GlobalTheory.fundamentalDomain_count_ae_eq_one | (intros; apply GlobalTheory.fundamentalDomain_count_ae_eq_one <;> assumption)
