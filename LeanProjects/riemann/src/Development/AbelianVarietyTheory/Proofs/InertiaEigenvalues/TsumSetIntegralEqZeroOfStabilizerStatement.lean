import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSetIntegralEqZeroOfStabilizer
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_setIntegral_eq_zero_of_stabilizer_integrals : ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G) [ν.IsMulLeftInvariant], SFinite ν → ∀ (Λ : Subgroup G), Countable Λ → ∀ 𝓖 : Set G, IsFundamentalDomain Λ 𝓖 ν → ∀ (a : Λ → X → X), (∀ x, a 1 x = x) → (∀ γ δ x, a (γ * δ) x = a γ (a δ x)) → ∀ F : X → G → ℂ, (∀ γ x g, F (a γ x) g = F x ((γ : G)⁻¹ * g)) → (∀ x, AEStronglyMeasurable (F x) ν) → ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν ≠ ⊤ → (∀ x (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x = x) → ∀ 𝓓 : Set G, IsFundamentalDomain Γ 𝓓 ν → IntegrableOn (F x) 𝓓 ν → ∫ g in 𝓓, F x g ∂ν = 0) → ∑' x, ∫ g in 𝓖, F x g ∂ν = 0 := by
  first | exact @GlobalTheory.tsum_setIntegral_eq_zero_of_stabilizer | exact GlobalTheory.tsum_setIntegral_eq_zero_of_stabilizer | (intros; apply GlobalTheory.tsum_setIntegral_eq_zero_of_stabilizer <;> assumption)
