import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSZeroSplit
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PtTransRec
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

set_option maxHeartbeats 800000 in

theorem lemK_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F) :
    Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Formalism.MainNotions.RamifiedCoefficientChains.Sh.LemK ((HW l).W K 1 LL h.2.2) := by
  intro l _ K LL hA' h5
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  have h1 := hA.1 l K 1 LL hA'.2.2
  have h11 := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs := (HW l).W_s K 1 LL hA'.2.2
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [(D.loc l).PD_p]; exact hA'.2.1
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hA'.2.2) :=
    (((h1.2.2.2.2.2.2.2.2.1 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hA'.2.2))) hs hp).2.2
      (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hA'.1)).1
  have tie := ((Cm l).C K 1 LL hA'.2.2).tie
  obtain ⟨hN, hAg⟩ := gam_of_tie _ hs tie
  exact lemK_of _ inferInstance (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL) h1.1 h1.2.2.1 (hL l K LL hA' h5)
    h1.2.2.2.2.1 h11.2.2 hring hN hAg (gamΔ_of_tie _ tie) (ptTrans_rec D HW F hP9 l K LL hA' h5)

end Formalism.MainNotions.N.Pv.LocalLengthBound
