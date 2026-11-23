import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineStabHaar

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

def SemidirectHaar.Statement (G T : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] : Prop :=
  ∀ (P H : Subgroup G), IsClosed (P : Set G) → IsClosed (H : Set G) → H ≤ P →
    ∀ (τ : T →* G) (β : P → T) (δ : T → ℝ≥0), Continuous τ → Continuous β → Continuous δ →
    (∀ t, τ t ∈ P) → (∀ t, ∀ x ∈ H, τ t * x * (τ t)⁻¹ ∈ H) → (∀ t, τ t ∈ H → t = 1) →
    (∀ p : P, (p : G) * (τ (β p))⁻¹ ∈ H) →
    ∀ (μ : Measure P) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
      (ρ : Measure T) [ρ.IsHaarMeasure],
    (∀ (t : T) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ t * x * (τ t)⁻¹) ∂ν = δ t * ∫⁻ x, f x ∂ν) →
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ p, φ p ∂μ = c * ∫⁻ t, δ t * ∫⁻ x : H, φ (x * τ t) ∂ν ∂ρ

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
