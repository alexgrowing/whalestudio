import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def FlagIntMuDegree.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ b : Ψ × Fin N →₀ ℕ,
    b.degree ≠ (rhoBlock Ψ N j).degree →
      flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * monomial b 1) = 0

example : (1 : ℕ) ≤ 2 ∧
    (Finsupp.single ((), (0 : Fin 2)) 1 : Unit × Fin 2 →₀ ℕ).degree ≠ (rhoBlock Unit 2 1).degree := by
  have hrho : rhoBlock Unit 2 1 = 0 := by
    ext ⟨u, i⟩
    fin_cases i <;> simp [rhoBlock]
  refine ⟨by norm_num, ?_⟩
  rw [hrho]
  simp

end GroundTheory.Heights₂.Heights.LowerBoundFree
