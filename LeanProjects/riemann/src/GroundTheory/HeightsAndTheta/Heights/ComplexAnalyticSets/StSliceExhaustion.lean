import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix
open scoped ContDiff

noncomputable section

def SliceExhaustion.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      ∃ f : ℕ → (Fin n → ℂ) → ℝ, (∀ k, ContDiff ℝ ∞ (f k)) ∧ (∀ k, HasCompactSupport (f k)) ∧
        (∀ k x, f k x ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ x, Tendsto (fun k => f k x) atTop (𝓝 1)) ∧
        Tendsto (fun k => varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (f k)
            (fun _ x => Real.log (h.dualNorm x))) atTop
          (𝓝 (varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ => 1)
            (fun _ x => Real.log (h.dualNorm x)))) ∧
        (∀ W ∈ (divCycle J u).support,
          Tendsto (fun k => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k)
              (fun _ x => Real.log (h.dualNorm x))) atTop
            (𝓝 (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (fun _ => 1)
              (fun _ x => Real.log (h.dualNorm x))))) ∧
        Tendsto (fun k =>
            varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log (h.dualNorm x))
                (vecCons (f k) fun _ x => Real.log (h.dualNorm x)) -
              varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log ‖linEval u x‖)
                (vecCons (f k) fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0)

end

end GroundTheory.Heights₂.Heights
