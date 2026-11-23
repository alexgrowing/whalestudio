import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

def VandermondeBranch.Statement : Prop :=
  ∀ (j : ℕ) (v : Fin j → ℚ),
    ∑ a, v a * (Matrix.vandermonde (Function.update v a (v a - 1))).det =
      (∑ a, v a - ∑ a : Fin j, ((a : ℕ) : ℚ)) * (Matrix.vandermonde v).det

end GroundTheory.Heights₂.Heights.LowerBoundFree
