import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOnOfIsCrys
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem crysOnCond_all : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), CrysOnCond D HW F :=
  fun D HW _ l _ K s LL h Y hY => GlobalTheory.CrysOnLevel.isCrysOn_of_isCrys D HW l K s LL h Y hY

end GlobalTheory
