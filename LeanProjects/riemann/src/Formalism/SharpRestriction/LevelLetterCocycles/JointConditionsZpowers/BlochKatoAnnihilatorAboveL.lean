import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem bloch_kato_annihilator_above_l (D : D7) (i : D.nd.Loc) (h55 : Formalism.MainNotions.LocalSituation.Conclusion5 D) (hO : LitGoodO) :
    Formalism.MainNotions.LargeLevelLemmas.BlochKatoAnnihilators (D := D) i := by
  intro w hw C _
  exact Formalism.MainNotions.LargeLevelLemmas.bkAAt_of_core (h := (h55 _ _).1) (hO := hO _ C.LL)

end Formalism.MainNotions.N
