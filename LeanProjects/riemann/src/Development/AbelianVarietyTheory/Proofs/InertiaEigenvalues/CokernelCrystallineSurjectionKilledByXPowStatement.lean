import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelCrystallineSurjectionKilledByXPow
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_crystalline_surjection_killed_by_X_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), lem3 D HW F := by
  first | exact @GlobalTheory.NL.CokerKill.X_pow_kills_coker | exact GlobalTheory.NL.CokerKill.X_pow_kills_coker | (intros; apply GlobalTheory.NL.CokerKill.X_pow_kills_coker <;> assumption)
