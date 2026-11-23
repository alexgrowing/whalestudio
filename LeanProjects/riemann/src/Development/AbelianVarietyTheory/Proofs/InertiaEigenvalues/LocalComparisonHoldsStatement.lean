import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_of_cmpOf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), p5eL D.loc D.locA HW F := by
  first | exact @GlobalTheory.NL.SandJumps.main | exact GlobalTheory.NL.SandJumps.main | (intros; apply GlobalTheory.NL.SandJumps.main <;> assumption)
