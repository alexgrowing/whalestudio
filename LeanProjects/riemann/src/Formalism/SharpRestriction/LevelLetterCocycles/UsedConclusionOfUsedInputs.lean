import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion

noncomputable section

namespace Formalism.MainNotions.DeltaInvariantLattices

open Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem thm1used_of_N1used {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    {C : CmpOf D.loc D.locA HW F} (h : DeltaInvariantNormBound D HW F C) : deltaInvariantLatticeGlobal D HW F C :=
  fun l _ K s LL g => ⟨h.1 l K s LL g, h.2.1 l K s LL g, h.2.2.1 l K s LL g, h.2.2.2.1 l K s LL g,
    h.2.2.2.2.1 l K s LL g, h.2.2.2.2.2.1 l K s LL g, h.2.2.2.2.2.2.1 l K s LL g,
    h.2.2.2.2.2.2.2.1 l K s LL g, h.2.2.2.2.2.2.2.2.1 l K s LL g, h.2.2.2.2.2.2.2.2.2.1 l K s LL g⟩

theorem proposition_two_of_used_inputs {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    {C : CmpOf D.loc D.locA HW F} (h : DeltaInvariantNormBound D HW F C) : prop2 D HW F :=
  (herr_prop_two_iff D HW F).2 ⟨h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem used_conclusion_of_used_inputs {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    {C : CmpOf D.loc D.locA HW F} (h : DeltaInvariantNormBound D HW F C) : UsedLocalConclusion D HW F C :=
  ⟨thm1used_of_N1used h, h.2.2.2.2.2.2.2.2.2.2.1, proposition_two_of_used_inputs h, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

end Formalism.MainNotions.DeltaInvariantLattices
