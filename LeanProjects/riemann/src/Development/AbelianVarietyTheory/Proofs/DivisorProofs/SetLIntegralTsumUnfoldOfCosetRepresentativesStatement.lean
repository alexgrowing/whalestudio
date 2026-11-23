import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralTsumUnfoldOfCosetRepresentatives
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setLIntegral_tsum_unfold_of_cosetRepresentatives : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (Γ Λ : Subgroup G) [Countable Γ] (T : Set Γ) (𝓕 D : Set G), μ.IsHaarMeasure → Λ ≤ Γ → (∀ γ : Γ, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : Γ) : G) ∈ Λ) → IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Λ D μ → ∀ f : G → ℝ≥0∞, Measurable f → (∀ γ ∈ Λ, ∀ g, f (γ * g) = f g) → ∫⁻ g in 𝓕, ∑' t : T, f (t.1.1 * g) ∂μ = ∫⁻ g in D, f g ∂μ := by
  first | exact @GlobalTheory.ResLine.setLIntegral_tsum_unfold | exact GlobalTheory.ResLine.setLIntegral_tsum_unfold | (intros; apply GlobalTheory.ResLine.setLIntegral_tsum_unfold <;> assumption)
