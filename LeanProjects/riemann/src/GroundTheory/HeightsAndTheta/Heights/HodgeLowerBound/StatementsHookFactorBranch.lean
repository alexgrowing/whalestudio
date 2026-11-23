import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

def hookFactor {j : ℕ} (u : Fin j → ℕ) : ℚ :=
  (Matrix.vandermonde fun r => (u r : ℚ)).det / ∏ r, ((u r).factorial : ℚ)

def HookFactorBranch.Statement : Prop :=
  ∀ (j : ℕ) (u : Fin j → ℕ),
    ∑ p, (if 0 < u p ∧ ∀ q, u q ≠ u p - 1 then hookFactor (Function.update u p (u p - 1)) else 0) =
      (∑ r, (u r : ℚ) - ∑ r : Fin j, ((r : ℕ) : ℚ)) * hookFactor u

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
