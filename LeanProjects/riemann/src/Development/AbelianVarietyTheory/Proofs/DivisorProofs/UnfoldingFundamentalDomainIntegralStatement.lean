import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFundamentalDomainIntegral
import Mathlib
open scoped NNReal ENNReal
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_fundamental_domain_integral : ∀ {G G₁ L Kt : Type} [Group G] [MeasurableSpace G] [Group G₁] [MeasurableSpace G₁] [MeasurableSpace L] [MeasurableSpace Kt] (μG : Measure G) (ν : Measure G₁) (μL : Measure L) (μK : Measure Kt) (N Q : Subgroup G) (Γ : Subgroup G₁) (μN : Measure N) (kk : Kt → G) (m : L → G₁ → G) (ι : G₁ → G) (w : L → ℝ≥0∞) (c : ℝ≥0∞) (dom : Set G₁) (𝓕 : Set N), Countable Q → Countable Γ → SFinite ν → SFinite μL → SFinite μN → (∀ g : G, Measurable (g * ·)) → (∀ g : G₁, Measurable (g * ·)) → (∀ g : G, Measurable (· * g)) → Measurable (fun p : N × G₁ × L × Kt => p.1.1 * m p.2.2.1 p.2.1 * kk p.2.2.2) → Measurable w → (∀ l, w l ≠ 0) → (∀ l, w l ≠ ⊤) → μG.IsMulLeftInvariant → (∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ g, φ g ∂μG = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ n, φ (n.1 * m l g₀ * kk k) * w l ∂μN ∂ν ∂μL ∂μK) → c ≠ 0 → c ≠ ⊤ → (∀ l g₀, ∀ γ ∈ Γ, m l (γ * g₀) = ι γ * m l g₀) → (∀ γ ∈ Γ, ι γ ∈ Q) → (∀ q ∈ Q, ∃! γ : Γ, (ι γ)⁻¹ * q ∈ N) → (∀ γ ∈ Γ, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ n, f (n.1 * ι γ) ∂μN = ∫⁻ n, f (ι γ * n.1) ∂μN) → μN.IsMulLeftInvariant → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μN → μN 𝓕 ≠ ⊤ → IsFundamentalDomain Γ dom ν → ν.IsMulLeftInvariant → ∀ 𝓓 : Set G, IsFundamentalDomain Q 𝓓 μG → ∀ f : G → ℝ≥0∞, AEMeasurable f μG → (∀ q ∈ Q, ∀ g, f (q * g) = f g) → (∀ n ∈ N, ∀ g, f (n * g) = f g) → ∫⁻ g in 𝓓, f g ∂μG ≤ c * μN 𝓕 * ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in dom, f (m l g₀ * kk k) * w l ∂ν ∂μL ∂μK := by
  first | exact @GlobalTheory.foldBound_le | exact GlobalTheory.foldBound_le | (intros; apply GlobalTheory.foldBound_le <;> assumption)
