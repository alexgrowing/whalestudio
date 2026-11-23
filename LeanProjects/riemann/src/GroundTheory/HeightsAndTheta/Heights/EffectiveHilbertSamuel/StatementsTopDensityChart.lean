import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.InhabitantsExtDelta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

open ExtInhabitants

def TopDensityChart.Statement : Prop :=
  ∀ (D : ℕ) (U : Type) [TopologicalSpace U] (A : FinHolAtlas D U)
    (L₂ L : HolLineBundle A) (m : ℕ) (ψ : Fin A.n → U → ℝ) (G : Fin A.n → U → ℂ),
    (∀ k l, ∀ x ∈ (A.chart k).source ∩ (A.chart l).source,
      ψ k x = ψ l x + Real.log (‖L₂.g k l x * L.g k l x ^ m‖ ^ 2)) →
    (∀ k l, ∀ x ∈ (A.chart k).source ∩ (A.chart l).source,
      G k x = jac A k l x * L₂.g k l x * L.g k l x ^ m * G l x) →
    ∀ (c : Fin A.n) (B : Set (Fin D → ℂ)), MeasurableSet B → B ⊆ (A.chart c).target →
      ∫⁻ y in B, ENNReal.ofReal (2 ^ D * ‖G c ((A.chart c).symm y)‖ ^ 2 *
        Real.exp (-ψ c ((A.chart c).symm y))) ≤ topNormSq A ψ G

end

end GroundTheory.Heights₂.Heights.EffectiveHS
