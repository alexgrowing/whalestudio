import Mathlib
import Formalism.PeriodIntegrals.ScPiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.HJSumSmulRight

noncomputable section

namespace PI.ScPiFrameW

open PI.ScPiExists

theorem frame_hypotheses_rank_one :
    let ε : Fin 4 → Bool := ![true, false, true, false]
    let e : Fin 1 → Fin 4 → ℂ := fun _ => ![1, 1, 0, 0]
    let f : Fin 1 → Fin 4 → ℂ := fun _ => ![1 / 2, -1 / 2, 0, 0]
    let z : Fin 4 → ℂ := ![0, 0, 0, 1]
    (4 = 2 * 1 + 1 + 1) ∧
    (∀ i : Fin 4, ε i = if i.val < 1 - 1 then true else decide ((i.val - (1 - 1)) % 2 = 0)) ∧
    (∀ a b, hJ ε (e a) (e b) = 0) ∧ (∀ a b, hJ ε (f a) (f b) = 0) ∧
    (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) ∧
    (∀ a, hJ ε (e a) z = 0 ∧ hJ ε (f a) z = 0) ∧ hJ ε z z = -((1 : ℝ) : ℂ) := by
  intro ε e f z
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> rfl
  · intro a b; simp [e, ε, hJ_eq_sum, sg, Fin.sum_univ_four]
  · intro a b; simp [f, ε, hJ_eq_sum, sg, Fin.sum_univ_four]; ring
  · intro a b
    have : a = b := Subsingleton.elim a b
    simp [this, e, f, ε, hJ_eq_sum, sg, Fin.sum_univ_four]; ring
  · intro a; simp [e, f, z, ε, hJ_eq_sum, sg, Fin.sum_univ_four]
  · simp [z, ε, hJ_eq_sum, sg, Fin.sum_univ_four]

theorem frame_hypotheses_rank_zero :
    let ε : Fin 2 → Bool := ![true, false]
    let z : Fin 2 → ℂ := ![0, 1]
    (2 = 2 * 0 + 1 + 1) ∧
    (∀ i : Fin 2, ε i = if i.val < 1 - 1 then true else decide ((i.val - (1 - 1)) % 2 = 0)) ∧
    hJ ε z z = -((1 : ℝ) : ℂ) := by
  intro ε z
  refine ⟨rfl, ?_, ?_⟩
  · intro i; fin_cases i <;> rfl
  · simp [z, ε, hJ_eq_sum, sg, Fin.sum_univ_two]

end PI.ScPiFrameW
