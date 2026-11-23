import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
import Mathlib
open NumberField IsDedekindDomain MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_fundamentalDomain_of_invariant_of_cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (f : G → ℂ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ := by
  first | exact @GlobalTheory.integrableOn_fundamentalDomain_of_cocompact | exact GlobalTheory.integrableOn_fundamentalDomain_of_cocompact | (intros; apply GlobalTheory.integrableOn_fundamentalDomain_of_cocompact <;> assumption)
