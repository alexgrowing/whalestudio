import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem family_scale_epsilon_condition {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.ArithmeticCylinders.FamilyExpDeficitBound' Fm) : Formalism.MainNotions.LocalQuadraticParts.IrreducibilityFamily Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hx)
  have := h x (le_trans (le_max_left _ _) hx) i
  unfold Formalism.MainNotions.LocalQuadraticParts.adm22
  rw [Fm.L_x x i hx1, Fm.L_ez x i]
  exact this

end Formalism.MainNotions.J

end
