import Formalism.YangianSpanCharacter.TJTrev

namespace Formalism.YangianSpanCharacter.P

open Matrix

theorem transpose_j_reversed : Formalism.YangianSpanCharacter.T.TJTrev := by
  intro R A _ _ _ q d di Y h1 h2 h3
  have hc : algebraMap R A Y * d = d * algebraMap R A Y := Algebra.commutes Y d
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.J, map_add, add_mul, mul_add]
  all_goals first
    | exact h1
    | exact h2
    | (rw [h3, hc]; abel)

end Formalism.YangianSpanCharacter.P
