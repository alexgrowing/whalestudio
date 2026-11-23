import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.ObjectsExtDelta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal ComplexConjugate

noncomputable section

def BergmanProj.Statement : Prop :=
  ∀ (D : ℕ) (U : Type) [TopologicalSpace U] [T2Space U] (A : FinHolAtlas D U)
    (L₂ L : HolLineBundle A) (m : ℕ) (ψ : Fin A.n → U → ℝ) (F₀ : Fin A.n → U → ℂ),
    (∀ k, ContinuousOn (ψ k ∘ (A.chart k).symm) (A.chart k).target) →
    (∀ k l, ∀ x ∈ (A.chart k).source ∩ (A.chart l).source,
      ψ k x = ψ l x + Real.log (‖L₂.g k l x * L.g k l x ^ m‖ ^ 2)) →
    (∀ k, ContinuousOn (F₀ k ∘ (A.chart k).symm) (A.chart k).target) →
    (∀ k l, ∀ x ∈ (A.chart k).source ∩ (A.chart l).source,
      F₀ k x = jac A k l x * L₂.g k l x * L.g k l x ^ m * F₀ l x) →
    topNormSq A ψ F₀ < ⊤ →
    ∃ F ∈ topSections A L₂ L m, topNormSq A ψ F < ⊤ ∧
      ∀ G ∈ topSections A L₂ L m, topNormSq A ψ G < ⊤ → chartInner A ψ (F₀ - F) G = 0

end

end GroundTheory.Heights₂.Heights.EffectiveHS
