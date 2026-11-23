import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem dimension_input_one_of_bloch_kato (D : D7) (h : Formalism.MainNotions.LocalSituation.Conclusion5 D) : Formalism.MainNotions.BlochKatoDuality.adm1 D := by
  intro l _ K
  exact (h l K).1

theorem dimension_input_two_of_bloch_kato (D : D7) (h : Formalism.MainNotions.LocalSituation.Conclusion5 D) : Formalism.MainNotions.BlochKatoDuality.adm2 D := by
  intro l _ K
  exact (h l K).2.2.2.1

end Formalism.MainNotions.N
