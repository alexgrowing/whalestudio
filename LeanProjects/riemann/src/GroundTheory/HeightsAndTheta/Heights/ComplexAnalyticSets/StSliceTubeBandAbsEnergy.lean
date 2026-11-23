import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBandAbsEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

def SliceTubeBandAbsEnergy.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      ∃ r₀ C : ℝ, ∀ r : ℝ, r₀ ≤ r →
        varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
              (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
                {y | r ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ r + 1}.indicator (fun _ => 1) x)
              (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) -
            varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
              (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
                {y | r ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ r + 1}.indicator (fun _ => 1) x *
                  Real.log (h.dualNorm x))
              (fun _ x => Real.log (h.dualNorm x)) ≤ C

end

end GroundTheory.Heights₂.Heights
