import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsGrassProdGeomDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def FlagIntMuOne.Statement : Prop :=
  ∀ (N j : ℕ), j ≤ N →
    flagInt Unit N (muPoly Unit N j ^ (j * (N - j)) * monomial (rhoBlock Unit N j) 1) =
      (-1) ^ (j * (N - j)) * grassDeg j (N - j)

example : (1 : ℕ) ≤ 2 := by norm_num

example : flagInt Unit 2 (muPoly Unit 2 1 ^ (1 * (2 - 1)) * monomial (rhoBlock Unit 2 1) 1) =
    (-1) ^ (1 * (2 - 1)) * grassDeg 1 (2 - 1) := by
  have hrho : rhoBlock Unit 2 1 = 0 := by
    ext ⟨u, i⟩
    fin_cases i <;> simp [rhoBlock]
  have h := Jint_line 1
  unfold Jint fib at h
  rw [vandBlocks_line, map_one, one_mul, dimN_line] at h
  rw [hrho, show (1 * (2 - 1) : ℕ) = 1 from rfl, monomial_zero', C_1, h]
  simp [grassDeg]

end GroundTheory.Heights₂.Heights.LowerBoundFree
