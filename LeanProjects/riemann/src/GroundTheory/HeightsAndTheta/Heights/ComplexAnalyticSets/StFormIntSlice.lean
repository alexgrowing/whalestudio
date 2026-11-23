import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutOffLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix
open scoped ContDiff

noncomputable section

variable {n : ℕ}

def FormIntSlice.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ) (a b : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) → ContinuousOn a {x | x ≠ 0} →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → b (t • x) = b x) → ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      formInt h W e a b =
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) a
          (vecCons b fun _ x => Real.log (h.dualNorm x))

end

end GroundTheory.Heights₂.Heights
