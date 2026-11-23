import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutBoundary
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceCutDecay.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 2) g → linForm ℓ ∉ W →
    IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A →
      ∃ C : ℝ, ∀ k : ℕ,
        (∫ y, chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
            (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) y) ≤ C / ((k : ℝ) + 1) ∧
          chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
              (vecCons (fun x => sliceCut h k x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) -
            chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A (sliceCut h k)
              (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) ≤ C / ((k : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights
