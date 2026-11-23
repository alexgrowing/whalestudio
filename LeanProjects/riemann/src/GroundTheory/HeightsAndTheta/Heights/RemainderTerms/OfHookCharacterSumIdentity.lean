import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableEqCardMonotone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.HookCharacterShiftIdentity

open Finset

def HookCharacterSumIdentitySmall.Statement : Prop :=
  ∀ r a : ℕ, 1 ≤ r → r ≤ a →
    (a : ℚ) * numStandardTable (fun i : Fin r => a + if (i : ℕ) = 0 then 1 else 0) =
      ∑ k ∈ Finset.Icc 2 (r + a), ∑ l ∈ Finset.range (min r k),
        (-1 : ℚ) ^ l * symmetricGroupCharacter (fun i => a + hookShape r k l i)
          ((k - 1) :: List.replicate (r * a + 1) 1)

end GroundTheory.Heights₂.Heights.RestTerms.HookCharacterShiftIdentity
