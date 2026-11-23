import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def FundCycleBaseChange.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) K)),
      fundCycle (J.map (MvPolynomial.map σ)) =
        ∑ W ∈ (fundCycle J).support, fundCycle J W • fundCycle (W.map (MvPolynomial.map σ))

end GroundTheory.Heights₂.Heights
