import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFundamentalDomainEqSumDoubleCosetUnfold
import Mathlib
open MeasureTheory
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_sum_doubleCoset_unfold : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ Ω : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → IsOpen (Ω : Set G) → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ Ω, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.Finite) → ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ i, IntegrableOn (fun k => f (h i * k)) Ω ν) → IntegrableOn f 𝓖 ν ∧ ∫ x in 𝓖, f x ∂ν = ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard : ℕ) : ℂ)⁻¹ * ∫ k in (Ω : Set G), f (h i * k) ∂ν := by
  first | exact @GlobalTheory.Unfold.integral_fundamentalDomain_eq_sum_unfold | exact GlobalTheory.Unfold.integral_fundamentalDomain_eq_sum_unfold | (intros; apply GlobalTheory.Unfold.integral_fundamentalDomain_eq_sum_unfold <;> assumption)
