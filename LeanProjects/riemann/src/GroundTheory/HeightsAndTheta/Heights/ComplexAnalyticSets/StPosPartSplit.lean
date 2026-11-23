import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPosPartIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def PosPartSplit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (E : ℕ → Set (Fin n → ℂ))
    (y : Fin d → ℂ),
    IsFiniteProjection J A → Pairwise (Function.onFun Disjoint E) →
    (∀ x ∈ fibre J A y, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ E k) →
      ENNReal.ofReal (chartPosDens J A f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J A ((E k).indicator f) φ y)

end

end GroundTheory.Heights₂.Heights
