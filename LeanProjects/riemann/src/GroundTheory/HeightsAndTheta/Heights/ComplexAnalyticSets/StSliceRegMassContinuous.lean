import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceRegMassContinuous.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (w : (Fin n → ℂ) → ℝ) (C : ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W → Measurable w → (∀ x, |w x| ≤ C) →
      ContinuousOn (fun ε => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) w
        (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) (Set.Ioi 0)

end

end GroundTheory.Heights₂.Heights
