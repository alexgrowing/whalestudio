import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

def PolyNonvanishDense.Statement : Prop :=
  ∀ (e : ℕ) (D : MvPolynomial (Fin e) ℚ), D ≠ 0 → Dense {y : Fin e → ℂ | aeval y D ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
