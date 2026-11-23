import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharactersGivenJumpsUnramifiedTwists
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_characters_given_jumps_unramified_twists : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.tableLineDegreeTwo.adm20 D HW F := by
  first | exact @GlobalTheory.CrysCharJumps.adm20_of_fonOf | exact GlobalTheory.CrysCharJumps.adm20_of_fonOf | (intros; apply GlobalTheory.CrysCharJumps.adm20_of_fonOf <;> assumption)
