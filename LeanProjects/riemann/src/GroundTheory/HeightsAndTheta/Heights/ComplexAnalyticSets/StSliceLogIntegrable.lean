import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def SliceLogIntegrable.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
      Integrable (chartAbsDens (J ⊔ Ideal.span {linForm ℓ - 1}) A
        (fun x => Real.log (h.dualNorm x) - Real.log ‖linEval u x‖)
        (fun _ x => Real.log (h.dualNorm x)))

end

end GroundTheory.Heights₂.Heights
