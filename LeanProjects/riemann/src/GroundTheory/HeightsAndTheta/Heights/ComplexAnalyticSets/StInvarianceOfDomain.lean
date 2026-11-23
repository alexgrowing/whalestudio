import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InvarianceOfDomain.Statement : Prop :=
  ∀ (n : ℕ) (U : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → Fin n → ℝ),
    IsOpen U → ContinuousOn f U → Set.InjOn f U → IsOpen (f '' U)

theorem InvarianceOfDomain.hypotheses_inhabited :
    IsOpen (Metric.ball (0 : Fin 2 → ℝ) 1) ∧
      ContinuousOn (fun x : Fin 2 → ℝ => ![x 0, x 1 + x 0 ^ 3]) (Metric.ball 0 1) ∧
      Set.InjOn (fun x : Fin 2 → ℝ => ![x 0, x 1 + x 0 ^ 3]) (Metric.ball 0 1) := by
  refine ⟨Metric.isOpen_ball, ?_, ?_⟩
  · refine Continuous.continuousOn ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using continuous_apply (0 : Fin 2)
    · have hc : Continuous (fun x : Fin 2 → ℝ => x 1 + x 0 ^ 3) := by fun_prop
      exact hc
  · intro s _ t _ hst
    have h0 : s 0 = t 0 := by simpa using congrFun hst 0
    have h1 : s 1 + s 0 ^ 3 = t 1 + t 0 ^ 3 := by simpa using congrFun hst 1
    funext i
    fin_cases i
    · exact h0
    · simp only [Fin.mk_one]
      rw [h0] at h1
      exact add_right_cancel h1

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
