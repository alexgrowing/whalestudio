import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def RatPrimeDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℚ)) (f : MvPolynomial σ ℚ), P.IsPrime → f ∉ P →
    {z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} ⊆
      closure {z : σ → ℂ | (∀ g ∈ P, aeval z g = 0) ∧ aeval z f ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
