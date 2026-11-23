import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPosPartIndependent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartChangeSheetNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ChartChangeLocal.Statement : Prop :=
  ∀ (n d : ℕ) (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (u u' : Fin n → ℂ) (U U' : Set (Fin n → ℂ)) (Φ Ψ : (Fin n → ℂ) → Fin n → ℂ)
    (f f' : (Fin n → ℂ) → ℝ) (φ φ' : Fin d → (Fin n → ℂ) → ℝ) (c : Fin d → ℝ)
    (g : Fin d → (Fin n → ℂ) → ℂ) (x' : Fin n → ℂ),
    IsOpen U → IsOpen U' → zeroSet J \ {x | linEval u x = 0} ⊆ U →
    zeroSet J' \ {x | linEval u' x = 0} ⊆ U' →
    DifferentiableOn ℂ Φ U' → DifferentiableOn ℂ Ψ U →
    Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}) →
    Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}) →
    (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x) →
    (∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x) →
    Measurable f → Measurable f' → (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, f' x = f (Φ x)) →
    (∀ k, SmoothNear (zeroSet J) (φ k)) → (∀ k, SmoothNear (zeroSet J') (φ' k)) →
    (∀ k, DifferentiableOn ℂ (g k) U') → (∀ k, ∀ x ∈ U', g k x ≠ 0) →
    (∀ k, ∀ x ∈ U', φ' k x = φ k (Φ x) + c k * Real.log ‖g k x‖) →
    x' ∈ zeroSet J' → linEval u' x' ≠ 0 → (∃ s', IsSheetAt J' A' x' s') →
    (∃ s, IsSheetAt J A (Φ x') s) →
      ∃ W' : Set (Fin n → ℂ), IsOpen W' ∧ x' ∈ W' ∧
        ∀ E' : Set (Fin n → ℂ), MeasurableSet E' → E' ⊆ W' →
          ∫⁻ y, ENNReal.ofReal (chartPosDens J' A' (E'.indicator f') φ' y) =
            ∫⁻ y, ENNReal.ofReal (chartPosDens J A ((Φ '' E').indicator f) φ y)

namespace ChartChange

def fsPot {n : ℕ} (x : Fin n → ℂ) : ℝ := Real.log (1 + euclPot x)

end ChartChange

end

end GroundTheory.Heights₂.Heights
