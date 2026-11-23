import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def IrreducibleConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (W J : Ideal (MvPolynomial σ ℂ)), W.IsPrime →
    IsPreconnected (zeroLocus ℂ W \ zeroLocus ℂ J)

end GroundTheory.Heights₂.Heights.HilbertSamuel
