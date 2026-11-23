import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

def ConeMapAreaOne.Statement : Prop :=
  ∀ (n e : ℕ) (U D : Set (Fin e → ℂ)) (v : (Fin e → ℂ) → (Fin n → ℂ))
    (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    IsOpen U → MeasurableSet D → D ⊆ U → DifferentiableOn ℂ v U →
    Set.InjOn (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) {q | q.1 ∈ D ∧ q.2 ≠ 0} →
    Measurable F →
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) ''
              {q | q.1 ∈ D ∧ q.2 ≠ 0}, F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∫⁻ x in D, ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)

end GroundTheory.Heights₂.Heights
