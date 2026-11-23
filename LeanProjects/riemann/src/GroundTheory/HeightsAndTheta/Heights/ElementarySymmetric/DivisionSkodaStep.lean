import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def skodaNormSq {D : ℕ} {U : Type} [TopologicalSpace U] (A : FinHolAtlas D U)
    (s : Fin D → Fin A.n → U → ℂ) (ψ : Fin A.n → U → ℝ) (t : ℝ) (F : Fin A.n → U → ℂ) : ℝ≥0∞ :=
  chartIntegral A fun j x =>
    ENNReal.ofReal (2 ^ D * ‖F j x‖ ^ 2 * (∑ i, ‖s i j x‖ ^ 2) ^ (-t) * Real.exp (-ψ j x))

def DivisionSkodaStep.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L D) (j : ℕ) (t : ℝ),
    2 ≤ D → (D : ℝ) - 1 < t → t ≤ j →
    ∀ F ∈ topSections X.A X.L₂ X.L (D + (j + 1)),
      skodaNormSq X.A Z.s (fun a x => φA.φ a x + ((j : ℝ) - t) * fsWeight X.e a x) (t + 1) F < ⊤ →
      ∃ h : Fin D → Fin X.A.n → X.U → ℂ,
        (∀ i, h i ∈ topSections X.A X.L₂ X.L (D + j) ∧
          skodaNormSq X.A Z.s (fun a x => φA.φ a x + ((j : ℝ) - t) * fsWeight X.e a x) t (h i) < ⊤) ∧
        F = ∑ i, Z.s i * h i

end

end GroundTheory.Heights₂.Heights.EffectiveHS
