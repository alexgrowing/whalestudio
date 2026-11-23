import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def BlockAltUnique.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ L : RootPoly Ψ N →ₗ[ℚ] ℚ,
    (∀ w, IsBlockPerm Ψ N j w → ∀ P, L (rename (weylAct Ψ N w) P) = weylSign Ψ N w * L P) →
    (∀ b : Ψ × Fin N →₀ ℕ, b.degree ≠ (rhoBlock Ψ N j).degree → L (monomial b 1) = 0) →
    ∀ P, L P = L (monomial (rhoBlock Ψ N j) 1) * blockInt Ψ N j P

example : ∃ L : RootPoly Unit 2 →ₗ[ℚ] ℚ, L ≠ 0 ∧
    (∀ w, IsBlockPerm Unit 2 1 w → ∀ P, L (rename (weylAct Unit 2 w) P) = weylSign Unit 2 w * L P) ∧
    (∀ b : Unit × Fin 2 →₀ ℕ, b.degree ≠ (rhoBlock Unit 2 1).degree → L (monomial b 1) = 0) := by
  have hrho : rhoBlock Unit 2 1 = 0 := by
    ext ⟨u, i⟩
    fin_cases i <;> simp [rhoBlock]
  have hw : ∀ w : Unit → Equiv.Perm (Fin 2), IsBlockPerm Unit 2 1 w → w = 1 := by
    unfold IsBlockPerm
    decide
  refine ⟨lcoeff ℚ 0, fun h => ?_, fun w hw' P => ?_, fun b hb => ?_⟩
  · have := LinearMap.congr_fun h 1
    simp at this
  · obtain rfl := hw w hw'
    have h1 : weylAct Unit 2 1 = id := by
      funext p
      rfl
    simp [h1, weylSign]
  · rw [hrho, map_zero] at hb
    have hb0 : b ≠ 0 := fun h => hb (by rw [h, map_zero])
    simp [coeff_monomial]
    exact hb0

end GroundTheory.Heights₂.Heights.LowerBoundFree
