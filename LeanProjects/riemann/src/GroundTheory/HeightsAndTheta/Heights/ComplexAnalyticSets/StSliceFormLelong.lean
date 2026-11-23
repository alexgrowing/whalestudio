import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormIntSlice
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix
open scoped ContDiff

noncomputable section

def SliceFormLelong.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (a : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ (divCycle W u').support, linForm ℓ ∉ P) →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) → ContDiffOn ℝ ∞ a {x | x ≠ 0} →
      Tendsto (fun ε => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) (𝓝[>] 0)
        (𝓝 (∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
            varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e a (fun _ x => Real.log (h.dualNorm x)) -
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a (fun _ x => Real.log (h.dualNorm x))))

end

end GroundTheory.Heights₂.Heights
