import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusions
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.SaturationArcLifting D HW F ∧ UnusedSlot80.SaturationEtale D HW F ∧ ArcLiftingSetup.SaturationFrobeniusPullback D HW F ∧ UnusedSlot80.GammaPreservesUniformiser D HW F ∧ UnusedSlot80.KillerAtLevels D HW F ∧ UnusedSlot80.KillerBoundWithConstant D HW F 8 ∧ UnusedSlot80.KillerAtLevelsSecondForm D HW F ∧ UnusedSlot80.FirstFiltrationArcLifting D HW F ∧ UnusedSlot80.FirstFiltrationEtale D HW F ∧ UnusedSlot80.SecondFiltrationArcLifting D HW F ∧ UnusedSlot80.SecondFiltrationEtale D HW F ∧ UnusedSlot80.FiltrationPropertiesEtale D HW F Cm ∧ UnusedSlot80.H1fBaseChangeFree D := by
  first | exact @GlobalTheory.ArcTools.arc_tools_from_clauses | exact GlobalTheory.ArcTools.arc_tools_from_clauses | (intros; apply GlobalTheory.ArcTools.arc_tools_from_clauses <;> assumption)
