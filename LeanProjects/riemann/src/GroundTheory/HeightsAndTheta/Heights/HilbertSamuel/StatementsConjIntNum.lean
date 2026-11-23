import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def ConjIntNum.Statement : Prop :=
  ∀ (K : Type) [DecidableEq K] (ι : K → Type) (F : Type) [Field F] (τ : F ≃+* F)
    (J : Ideal (MvPolynomial (Σ k, ι k) F)) (n : ℕ) (bs : Fin n → K → ℤ),
    NumbersDVR.intNum F (J.map (MvPolynomial.map (τ : F →+* F))) bs = NumbersDVR.intNum F J bs

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
