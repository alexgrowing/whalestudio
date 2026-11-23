import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PointIdealMultiProj.Statement : Prop :=
  ∀ (F : Type) [Field F] (L : Type) [Field L] [Algebra F L]
    (K : Type) [DecidableEq K] (ι : K → Type) (z : (Σ k, ι k) → L),
    (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → IsMultiProjPrime (pointIdeal F z)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
