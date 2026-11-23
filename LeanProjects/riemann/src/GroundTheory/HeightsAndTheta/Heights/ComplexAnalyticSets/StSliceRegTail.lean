import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormLelong
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceRegTail.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (a : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ (divCycle W u').support, linForm ℓ ∉ P) →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) → ContinuousOn a {x | x ≠ 0} →
      ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k, K ≤ k → ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        |varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a
            (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) -
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => sliceCut h k x * a x)
            (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))| ≤ δ

end

end GroundTheory.Heights₂.Heights
