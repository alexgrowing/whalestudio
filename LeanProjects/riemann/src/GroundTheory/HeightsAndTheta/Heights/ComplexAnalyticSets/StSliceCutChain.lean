import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix

noncomputable section

def SliceCutChain.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ) (k : ℕ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
      varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log (h.dualNorm x))
          (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) -
        varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log ‖linEval u x‖)
          (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) =
      -((k : ℝ) + 1)⁻¹ *
          varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
            (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) *
              deriv Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1)))
            (fun _ x => Real.log (h.dualNorm x)) +
        ((k : ℝ) + 1)⁻¹ ^ 2 *
          (varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
              (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) *
                deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1)))
              (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) -
            varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
              (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) *
                deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1)) *
                Real.log (h.dualNorm x))
              (fun _ x => Real.log (h.dualNorm x)))

end

end GroundTheory.Heights₂.Heights
