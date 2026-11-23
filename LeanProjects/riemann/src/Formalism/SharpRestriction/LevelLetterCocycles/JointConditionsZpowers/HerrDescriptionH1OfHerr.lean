import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.WachRestrictionOfLiftingPackage
import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapInjectiveBijectiveNorms
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem herr_description_H1_of_herr (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F) : Formalism.MainNotions.DeltaInvariantLattices.adm2 D HW F := by
  intro l _ K s LL hg T _ _
  refine ⟨(h l K s LL hg).2.1 T, fun _ hp => ?_⟩
  have hA := (h l K s LL hg).1 (fun e => absurd e hp) T
  exact ⟨hA.1, fun w => hA.2.1 w⟩

end Formalism.MainNotions.N
