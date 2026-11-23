import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutOffLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceCutBoundary.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
    (F G : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) g → linForm ℓ ∉ W →
    IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → F (t • x) = F x) →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → G (t • x) = G x) →
    ContDiffOn ℝ ∞ F {x | x ≠ 0} → ContDiffOn ℝ ∞ G {x | x ≠ 0} →
      Tendsto (fun k =>
          chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A G
              (vecCons (fun x => sliceCut h k x * F x) fun _ x => Real.log (h.dualNorm x)) -
            chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => sliceCut h k x * G x)
              (vecCons F fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0)

end

end GroundTheory.Heights₂.Heights
