import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def SliceAbsIndep.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ ℓ' : Fin n → ℂ)
    (A A' : Matrix (Fin (e + 1)) (Fin n) ℂ) (w : (Fin n → ℂ) → ℝ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm ℓ ∉ J → linForm ℓ' ∉ J →
    IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
    IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ' - 1}) A' →
    Measurable w → (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → w (t • x) = w x) →
      ∫⁻ y, ENNReal.ofReal (chartAbsDens (J ⊔ Ideal.span {linForm ℓ - 1}) A w
          (fun _ x => Real.log (h.dualNorm x)) y) =
        ∫⁻ y, ENNReal.ofReal (chartAbsDens (J ⊔ Ideal.span {linForm ℓ' - 1}) A' w
          (fun _ x => Real.log (h.dualNorm x)) y)

end

end GroundTheory.Heights₂.Heights
