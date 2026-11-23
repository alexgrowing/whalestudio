import Formalism.SharpRestriction.LevelLetterCocycles.FirstFrameStepImplication
import Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
import Formalism.SharpRestriction.LevelLetterCocycles.DdRFull

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def FirstFrameOfModels : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    adm1 D HW F Cm → DdRFull D → DiRank D HW F Cm → modelLR D HW → modelFR D HW → u1R D HW

theorem first_frame_of_models (hL : FirstFrameOfModels) (hML : ModelLStep) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
      DdRFull D → DiRank D HW F Cm → Adm1 D HW F Cm CA CB CK → modelFR D HW → u1R D HW :=
  fun D HW F Cm CA CB CK hd hr hA hMF => hL D HW F Cm hA.1 hd hr (hML D HW F Cm CA CB CK hA) hMF

end Formalism.MainNotions.N.Ln34

end
