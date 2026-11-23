import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsGrassProdGeomDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def FlagIntProjection.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ P : RootPoly Ψ N,
    flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * P) =
      (-1) ^ dimN Ψ N j * grassProdDeg (Fintype.card Ψ) j (N - j) * blockInt Ψ N j P

example : (1 : ℕ) ≤ 2 := by norm_num

example : flagInt Unit 2 (muPoly Unit 2 1 ^ dimN Unit 2 1 * vandBlocks Unit 2 1) =
    (-1) ^ dimN Unit 2 1 * grassProdDeg (Fintype.card Unit) 1 (2 - 1) * blockInt Unit 2 1 (vandBlocks Unit 2 1) := by
  have h := Jint_line 1
  unfold Jint fib at h
  rw [map_one, one_mul] at h
  rw [h, ← fdeg, fdeg_line, dimN_line]
  simp [grassProdDeg, grassDeg]

end GroundTheory.Heights₂.Heights.LowerBoundFree
