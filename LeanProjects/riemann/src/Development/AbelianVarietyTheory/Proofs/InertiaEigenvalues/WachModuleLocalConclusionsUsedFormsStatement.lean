import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModuleLocalConclusions_usedForms : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm ∧ DeltaInvariantLattices.ConclusionE D HW F := by
  first | exact @GlobalTheory.NL.usedLocalConclusion_and_prvE | exact GlobalTheory.NL.usedLocalConclusion_and_prvE | (intros; apply GlobalTheory.NL.usedLocalConclusion_and_prvE <;> assumption)
