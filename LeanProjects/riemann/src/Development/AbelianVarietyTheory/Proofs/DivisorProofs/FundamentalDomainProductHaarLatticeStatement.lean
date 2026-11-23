import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainProductHaarLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_product_haar_lattice : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup G) (Δ : Subgroup H) [Countable Γ] [Countable Δ] (μ : Measure G) (ν : Measure H), μ.IsHaarMeasure → ν.IsHaarMeasure →
    ∀ (𝓕 : Set G) (𝓖 : Set H), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Δ 𝓖 ν →
    (∃ C : Set G, IsCompact C ∧ ∀ g, ∃ γ ∈ Γ, ∃ c ∈ C, g = γ * c) → (∃ C : Set H, IsCompact C ∧ ∀ h, ∃ γ ∈ Δ, ∃ c ∈ C, h = γ * c) →
    ∀ θ : G → H → ℂ, Continuous (fun p : G × H => θ p.1 p.2) → (∀ γ ∈ Γ, ∀ δ ∈ Δ, ∀ g h, θ (γ * g) (δ * h) = θ g h) →
    (∀ h, ∫ g in 𝓕, θ g h ∂μ = 0) → ∫ g in 𝓕, (⨍ h in 𝓖, θ g h ∂ν) ∂μ = 0 := by
  first | exact @GlobalTheory.DblBox.integral_setAverage_eq_zero_of_cocompact | exact GlobalTheory.DblBox.integral_setAverage_eq_zero_of_cocompact | (intros; apply GlobalTheory.DblBox.integral_setAverage_eq_zero_of_cocompact <;> assumption)
