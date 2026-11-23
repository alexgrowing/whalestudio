import Mathlib
import Formalism.PeriodIntegrals.ScalRelRepFree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarRelationReflexive.IsScalarRefl

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scalar_rep_free (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalRelRepFree.ScalarRepFree D u u' := by
  intro F0 Λ hrow x y y' hrel hsc
  obtain ⟨n, hn, m, hm, hfr, hzt⟩ := hrel
  exact PI.UnitaryGroupMassFormula.ScalRelRepFree.scalRel_move Λ hrow.2.1.1 _ _ (lf D F0) x.1.1 y.1.1 y'.1.1 n m
    ⟨hrow.2.1.2.2.1, y.1.2.1, hn, hm, hfr, hzt⟩ hsc

end
