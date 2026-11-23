import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

def ReesAlgebraDim.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (I : Ideal A), I ≠ ⊥ →
    ∀ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) → ringKrullDim (reesAlgebra I) = ((n + 1 : ℕ) : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights.NumbersDVR
