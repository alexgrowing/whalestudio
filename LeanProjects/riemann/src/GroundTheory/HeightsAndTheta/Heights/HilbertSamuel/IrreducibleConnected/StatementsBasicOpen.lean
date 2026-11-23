import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def IrreducibleBasicOpenConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (W : Ideal (MvPolynomial σ ℂ)) (g : MvPolynomial σ ℂ), W.IsPrime → g ∉ W →
    IsPreconnected (zeroLocus ℂ W \ {x : σ → ℂ | eval x g = 0})

end GroundTheory.Heights₂.Heights.HilbertSamuel
