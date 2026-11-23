import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory ReciprocityTheory.AnForm.M

def PushForwardOpen.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) → ∀ (q : X → Fin e → ℂ) (O : Set X),
    IsOpen O →
    (∀ x ∈ O, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) →
    (∀ j, ∀ᵐ u, u ∈ (A.chart j).target → (A.chart j).symm u ∉ O → locDens A Φ j u = 0) →
    (∀ᵐ y, (q ⁻¹' {y} ∩ O).Finite) →
    ∀ g : X → ℝ, MIntegrable A Φ g →
      Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} ∩ O, g x * pushDens A Φ q x) ∧
        mInt A Φ g = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} ∩ O, g x * pushDens A Φ q x

end GroundTheory.Heights₂.Heights.Targets
