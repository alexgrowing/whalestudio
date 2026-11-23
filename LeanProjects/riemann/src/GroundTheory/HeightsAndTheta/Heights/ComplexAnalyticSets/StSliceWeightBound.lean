import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix

noncomputable section

def SliceWeightBound.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
      ∃ C : ℝ, ∀ (w : (Fin n → ℂ) → ℝ) (M : ℝ), Measurable w → (∀ x, |w x| ≤ M) →
        |varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
            (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) * w x)
            (fun _ x => Real.log (h.dualNorm x))| ≤ C * M

end

end GroundTheory.Heights₂.Heights
