import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def MinimalPrimeComap.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] (σ : K →+* L) (ι : Type) (I : Ideal (MvPolynomial ι K)),
    I.IsPrime → ∀ P ∈ (I.map (MvPolynomial.map σ)).minimalPrimes,
      P.comap (MvPolynomial.map σ) = I

end GroundTheory.Heights₂.Heights
