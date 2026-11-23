import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModule_uniqueness_characterisation : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), WachCharacterisation D HW F := by
  first | exact @GlobalTheory.NL.FrobeniusMatrixUniqueness.main | exact GlobalTheory.NL.FrobeniusMatrixUniqueness.main | (intros; apply GlobalTheory.NL.FrobeniusMatrixUniqueness.main <;> assumption)
