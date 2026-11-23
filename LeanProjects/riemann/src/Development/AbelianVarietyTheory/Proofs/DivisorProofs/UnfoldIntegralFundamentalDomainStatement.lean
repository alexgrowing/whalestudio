import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldIntegralFundamentalDomain
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_integral_fundamental_domain : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (Q : Type) [Countable Q]
    (act : Q → Γ → Q) (T : Q → G → ℂ) (f : G → ℂ),
    IsFundamentalDomain Γ 𝓕 μ → (∀ q, act q 1 = q) → (∀ q a b, act (act q a) b = act q (a * b)) →
    (∀ q (δ : Γ) x, T q ((δ : G) * x) = T (act q δ) x) → (∀ q, AEStronglyMeasurable (T q) μ) →
    (∀ δ ∈ Γ, ∀ x, f (δ * x) = f x) → AEStronglyMeasurable f μ →
    ∫⁻ x in 𝓕, ‖f x‖ₑ * ∑' q, ‖T q x‖ₑ ∂μ ≠ ⊤ →
    (∀ q (S : Subgroup G), (∀ g, g ∈ S ↔ ∃ hg : g ∈ Γ, act q ⟨g, hg⟩ = q) → ∀ D : Set G, IsFundamentalDomain S D μ →
      IntegrableOn (fun x => f x * T q x) D μ → ∫ x in D, f x * T q x ∂μ = 0) →
    ∫ x in 𝓕, f x * ∑' q, T q x ∂μ = 0 := by
  first | exact @GlobalTheory.UnfoldOrbits.integral_mul_tsum_eq_zero | exact GlobalTheory.UnfoldOrbits.integral_mul_tsum_eq_zero | (intros; apply GlobalTheory.UnfoldOrbits.integral_mul_tsum_eq_zero <;> assumption)
