import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Expand
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def LemmaBLast.Statement : Prop :=
  ∀ (r a : ℕ), ∃ κ : ℚ,
    (κ = (r.factorial : ℚ) * a.factorial ∨ κ = -((r.factorial : ℚ) * a.factorial)) ∧
    ∀ lam : Fin r → ℕ, Antitone lam →
      dividedDifference 1 (r + a)
          (aeval (yRoot 1 r a SmallBlock.last 0) (schur (Fin r) lam) *
            vandermondeOf (yRoot 1 r a SmallBlock.last 0) *
              vandermondeOf (zRoot 1 r a SmallBlock.last 0)) =
        if ∀ i, a ≤ lam i then
          algebraMap (RootRing 1 (r + a)) (FractionRing (RootRing 1 (r + a)))
            (C κ * aeval (fun i : Fin (r + a) => C SmallBlock.last.sign * X ((0 : Fin 1), i))
              (schur (Fin (r + a)) (fun i => lam i - a)))
        else 0

namespace VandermondePushforward

def emb (j k : ℕ) : Fin (j + k) → Fin 1 × Fin (k + j) :=
  fun i => (0, Fin.cast (Nat.add_comm j k) i)

end VandermondePushforward

end

end GroundTheory.Heights₂.Heights.RestTerms
