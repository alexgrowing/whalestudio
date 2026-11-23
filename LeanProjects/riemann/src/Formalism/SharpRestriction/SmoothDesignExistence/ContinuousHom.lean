import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

def FontAll (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l), TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(Loc.OL LL)

theorem font_of_all_places {D : D7} (h : FontAll D) (i : D.nd.Loc) : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i :=
  fun w hw C => h (D.nd.l i) (D.nbr i w hw).Kw C.LL

end Formalism.MainNotions.Pk

end
