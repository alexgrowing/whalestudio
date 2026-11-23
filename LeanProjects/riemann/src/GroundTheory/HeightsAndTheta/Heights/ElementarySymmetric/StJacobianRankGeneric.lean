import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameJacobianGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def genericGradient {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    Fin n → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J) :=
  fun l => algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
    (Ideal.Quotient.mk J (pderiv l f))

def JacobianRankGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime],
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      Module.finrank (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
        (Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (genericGradient J '' (J : Set _))) ≤ n - d

end

end GroundTheory.Heights₂.Heights
