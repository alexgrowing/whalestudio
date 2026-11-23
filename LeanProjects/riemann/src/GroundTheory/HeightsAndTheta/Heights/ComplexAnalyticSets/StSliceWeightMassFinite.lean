import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutOffLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def SliceWeightMassFinite.Statement : Prop :=
  ∀ (n d : ℕ) (h : HermNorm n) (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin d) (Fin n) ℂ) (a : (Fin n → ℂ) → ℝ),
    I.IsPrime → linForm ℓ - 1 ∈ I → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = d →
    IsFiniteProjection I A →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) → ContinuousOn a {x | x ≠ 0} →
      Integrable (chartAbsDens I A a (fun _ x => Real.log (h.dualNorm x)))

end

end GroundTheory.Heights₂.Heights
