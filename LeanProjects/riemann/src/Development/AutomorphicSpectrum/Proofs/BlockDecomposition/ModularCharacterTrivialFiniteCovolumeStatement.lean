import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterTrivialFiniteCovolume
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodular
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuotientMeasureTower
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modular_character_trivial_finite_covolume : ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (Γ₁ : Subgroup G₁) [Countable Γ₁] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁), IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → ∀ δ : G₁ →* ℝ≥0, Measurable δ → (∀ γ ∈ Γ₁, δ γ = 1) → ∀ u, δ u = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain | exact GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain <;> assumption)
