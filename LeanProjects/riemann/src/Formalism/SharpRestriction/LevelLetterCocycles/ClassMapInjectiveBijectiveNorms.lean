import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

noncomputable section

namespace Formalism.MainNotions.LocalSituation

open Formalism.BasicNotions Formalism.BasicNotions.Loc

def ClassMapInjectiveBijectiveNorms (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    HerrAat (sit D.loc HW l (D.locA l) K s LL h) ∧ HerrAsat (sit D.loc HW l (D.locA l) K s LL h) ∧
      ((HW l).W K s LL h).ClNat

theorem classMapInjectiveBijectiveNorms_of_aux6 {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    (h : Conclusion6 D HW F) : ClassMapInjectiveBijectiveNorms D HW F :=
  fun l _ K s LL g => ⟨(h l K s LL g).1, (h l K s LL g).2.1, (h l K s LL g).2.2.1⟩

end Formalism.MainNotions.LocalSituation
