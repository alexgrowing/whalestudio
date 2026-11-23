import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def BranchInComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (k : ℕ) (q : Fin n → ℂ) (c : VarBranch I k q),
    ∃ J ∈ I.minimalPrimes, Set.MapsTo c.toFun (Metric.ball 0 c.radius) (zeroSet J)

def axisBranch : VarBranch (Ideal.span {X 0 * X 1} : Ideal (MvPolynomial (Fin 2) ℂ)) 1 0 where
  radius := 1
  radius_pos := one_pos
  toFun t := fun i ↦ if i = 0 then t 0 else 0
  differentiableOn := by
    refine Differentiable.differentiableOn (differentiable_pi.2 fun i ↦ ?_)
    by_cases hi : i = 0
    · simp only [hi, if_true]
      exact differentiable_apply 0
    · simp only [hi, if_false]
      exact differentiable_const 0
  injOn := by
    intro s _ t _ hst
    have h0 := congrFun hst 0
    simp only [if_true] at h0
    funext i
    rw [Subsingleton.elim i 0]
    exact h0
  map_zero := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  mapsTo := by
    intro t _ g hg
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    simp

end

end GroundTheory.Heights₂.Heights
