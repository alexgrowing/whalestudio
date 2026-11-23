import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceRegVarBound.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (ε C : ℝ)
    (b₁ b₂ w : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W → 0 < ε →
    Measurable b₁ → Measurable b₂ → Measurable w →
    (∀ x, |b₁ x| ≤ C) → (∀ x, |b₂ x| ≤ C) → (∀ x, w x ∈ Set.Icc (0 : ℝ) 1) →
    (∀ x, |b₁ x - b₂ x| ≤ C * w x) →
      |varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b₁
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) -
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) b₂
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))| ≤
        C * (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) w
            (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) +
          2 * varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) w
            (fun _ x => Real.log (h.dualNorm x)))

end

end GroundTheory.Heights₂.Heights
