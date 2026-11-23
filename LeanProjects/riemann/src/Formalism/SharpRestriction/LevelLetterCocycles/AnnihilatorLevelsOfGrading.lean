import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

def KillLevFacts (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => LevGrad ((HW l).W K 1 LL hG)

theorem annihilator_levels_of_grading (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hK : KillLevFacts D HW) : KillerLevelsTheorem D HW F Cm := by
  rintro ⟨-, h9⟩
  intro l _ K LL hG hC h5
  have hfd : FiniteDimensional (Padic l) ↥(K0 K) := by
    first
    | exact inferInstance
    | exact ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank (Padic l) ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hC
  have hT := tool_algebra_of_ring_condition D HW F h9 l K LL hC h5
  exact KL.killerLevCore_of _ (KF.psUnitE_of _ hR hT) (KF.psCoprime_of _ hR) (hK l K LL hG hC h5)
    (KF.psStable_of _ hR) hR.1

end Formalism.MainNotions.UnusedSlot80
