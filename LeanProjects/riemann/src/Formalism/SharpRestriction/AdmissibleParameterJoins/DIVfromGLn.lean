import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLk
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLm
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLf

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem family_four_choice_conditions {eps : ℝ} (Fm : FamP eps) (C0 CH : ℝ) (h : ChosenE Fm C0 CH) : LocalQuadraticParts.ChosenLeadingTermsCountFamily Fm := by
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  exact h.2.1

theorem family_bad_choice_bound {eps : ℝ} (Fm : FamP eps) (C0 CH : ℝ) (h : ChosenE Fm C0 CH) : LocalQuadraticParts.FewBadOrbitsFamily Fm := by
  obtain ⟨_, _, Cb, _, _, hb, h⟩ := h
  exact ⟨Cb, hb, h.2.2.1⟩

end Formalism.MainNotions.J

end
