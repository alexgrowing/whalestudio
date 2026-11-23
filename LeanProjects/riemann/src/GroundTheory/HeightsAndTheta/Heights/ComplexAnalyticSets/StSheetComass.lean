import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaMultiplicity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

variable {n d : ℕ}

def sheetJac (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ) : ℝ :=
  areaJacobian ((WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
    ((fderiv ℝ s y : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℝ] (Fin n → ℂ)) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap)

theorem sheetJac_nonneg (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ) : 0 ≤ sheetJac s y :=
  Real.sqrt_nonneg _

def SheetComass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ), (∀ k, SmoothNear (zeroSet J) (φ k)) →
    ∃ C : ℝ, ∀ x ∈ zeroSet J ∩ Metric.closedBall 0 R, ∀ s : (Fin d → ℂ) → Fin n → ℂ, IsSheetAt J A x s →
      |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ x)| ≤ C * sheetJac s (A *ᵥ x)

end

end GroundTheory.Heights₂.Heights
