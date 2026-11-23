import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaneSliceMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceFormMass.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (c : Fin (e + 1) → ℝ) (ψ : Fin (e + 1) → (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W →
    IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → f (t • x) = f x) → ContinuousOn f {x | x ≠ 0} →
    (∀ (k : Fin (e + 1)) (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → ψ k (t • x) = ψ k x) →
    (∀ k, ContDiffOn ℝ ∞ (ψ k) {x | x ≠ 0}) →
      Integrable (chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A f
        (fun k x => c k * Real.log (h.dualNorm x) + ψ k x))

end

end GroundTheory.Heights₂.Heights
