import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def matGauss {m n : ℕ} (π : Fin m → Fin n → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2))

def ConeFibreAverage.Statement : Prop :=
  ∀ n m : ℕ, ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧
    ∀ (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J →
      (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
        ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
            ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
          K * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J}

theorem ConeFibreAverage.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      ∀ᵐ π : Fin 1 → Fin 1 → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 1),
        fibreCount (HermNorm.std 1) ⊥ π w ≠ ⊤ := by
  obtain ⟨hJ, hfib⟩ := ConeMassOfFibre.hypotheses_inhabited
  refine ⟨hJ, ?_⟩
  filter_upwards [hfib] with π hπ
  filter_upwards [hπ] with w hw
  rw [hw]
  exact ENat.natCast_ne_top 1

end

end GroundTheory.Heights₂.Heights
