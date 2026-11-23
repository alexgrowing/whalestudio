import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.InhabitantsExtDelta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def BergmanComplete.Statement : Prop :=
  ∀ (D : ℕ) (U : Type) [TopologicalSpace U] (A : FinHolAtlas D U)
    (L₂ L : HolLineBundle A) (m : ℕ) (ψ : Fin A.n → U → ℝ),
    (∀ k, ContinuousOn (ψ k ∘ (A.chart k).symm) (A.chart k).target) →
    (∀ k l, ∀ x ∈ (A.chart k).source ∩ (A.chart l).source,
      ψ k x = ψ l x + Real.log (‖L₂.g k l x * L.g k l x ^ m‖ ^ 2)) →
    ∀ G : ℕ → Fin A.n → U → ℂ, (∀ n, G n ∈ topSections A L₂ L m) →
    (∀ n, topNormSq A ψ (G n) < ⊤) →
    Tendsto (fun p : ℕ × ℕ => topNormSq A ψ (G p.1 - G p.2)) atTop (𝓝 0) →
    ∃ F ∈ topSections A L₂ L m, topNormSq A ψ F < ⊤ ∧
      Tendsto (fun n => topNormSq A ψ (G n - F)) atTop (𝓝 0)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
