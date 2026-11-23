import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem SpecFirstRename.proof : SpecFirstRename.Statement := by
  intro n k f u u'
  simp only [specFirst, bind₁_bind₁, bind₁_rename]
  refine congrArg (fun φ => bind₁ φ f) (funext fun ij => ?_)
  obtain ⟨i, j⟩ := ij
  have one : (1 : Fin (k + 1 + 1)) = Fin.succ 0 := Fin.succ_zero_eq_one.symm
  cases i using Fin.cases with
  | zero =>
    show (bind₁ (specFirstVar u')) (specFirstVar u (Equiv.swap (0 : Fin (k + 1 + 1)) 1 0, j)) =
      (bind₁ (specFirstVar u)) (specFirstVar u' (0, j))
    rw [Equiv.swap_apply_left, one]
    simp only [specFirstVar, Fin.cases_succ, Fin.cases_zero, bind₁_X_right, bind₁_C_right]
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      show (bind₁ (specFirstVar u'))
          (specFirstVar u (Equiv.swap (0 : Fin (k + 1 + 1)) 1 (Fin.succ 0), j)) =
        (bind₁ (specFirstVar u)) (specFirstVar u' (Fin.succ 0, j))
      have h : Equiv.swap (0 : Fin (k + 1 + 1)) 1 (Fin.succ 0) = 0 := by
        rw [← one]; exact Equiv.swap_apply_right _ _
      rw [h]
      simp only [specFirstVar, Fin.cases_succ, Fin.cases_zero, bind₁_X_right, bind₁_C_right]
    | succ i =>
      show (bind₁ (specFirstVar u'))
          (specFirstVar u (Equiv.swap (0 : Fin (k + 1 + 1)) 1 (Fin.succ (Fin.succ i)), j)) =
        (bind₁ (specFirstVar u)) (specFirstVar u' (Fin.succ (Fin.succ i), j))
      have h : Equiv.swap (0 : Fin (k + 1 + 1)) 1 (Fin.succ (Fin.succ i)) = Fin.succ (Fin.succ i) := by
        refine Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ?_
        rw [one]
        exact fun h' => Fin.succ_ne_zero i (Fin.succ_injective _ h')
      rw [h]
      simp only [specFirstVar, Fin.cases_succ, bind₁_X_right]

end GroundTheory.Heights₂.Heights
