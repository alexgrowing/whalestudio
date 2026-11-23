import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIndependentIntegral
import Mathlib

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_independent_integral : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (H : Subgroup G) (ν : Measure H) [SFinite ν], MeasurePreserving (fun p : H => p⁻¹) ν ν → ∀ 𝓓₁ 𝓓₂ : Set G, NullMeasurableSet 𝓓₁ μ → NullMeasurableSet 𝓓₂ μ → ∀ c₁ c₂ : ENNReal, (∀ᵐ g ∂μ, ν {p : H | (p : G) * g ∈ 𝓓₁} = c₁) → (∀ᵐ g ∂μ, ν {p : H | (p : G) * g ∈ 𝓓₂} = c₂) → ∀ φ : G → ENNReal, AEMeasurable φ μ → (∀ p ∈ H, ∀ g, φ (p * g) = φ g) → c₂ * ∫⁻ g in 𝓓₁, φ g ∂μ = c₁ * ∫⁻ g in 𝓓₂, φ g ∂μ := by
  first | exact @GlobalTheory.const_mul_setLIntegral_eq_of_slice_measure | exact GlobalTheory.const_mul_setLIntegral_eq_of_slice_measure | (intros; apply GlobalTheory.const_mul_setLIntegral_eq_of_slice_measure <;> assumption)
