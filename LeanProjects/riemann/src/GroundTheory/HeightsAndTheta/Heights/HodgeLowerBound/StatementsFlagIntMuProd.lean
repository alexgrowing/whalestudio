import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def FlagIntMuProd.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N →
    flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * monomial (rhoBlock Ψ N j) 1) =
      ((dimN Ψ N j).factorial : ℚ) / ((j * (N - j)).factorial : ℚ) ^ Fintype.card Ψ *
        flagInt Unit N (muPoly Unit N j ^ (j * (N - j)) * monomial (rhoBlock Unit N j) 1) ^ Fintype.card Ψ

example : (1 : ℕ) ≤ 2 := by norm_num

end GroundTheory.Heights₂.Heights.LowerBoundFree
