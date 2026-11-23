import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RatChartObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

def RatSheetSumMeasurable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (Φ : ℝ → ℝ → ℝ) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    (∀ y, (RatChart.ratFibre J p q y).Finite) → Measurable (Function.uncurry Φ) → Measurable g →
      Measurable fun y => RatChart.ratSheetSum J p q
        (fun x s => Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y)) y

end GroundTheory.Heights₂.Heights
