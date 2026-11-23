import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LocalSituation.Conclusion4 D HW F := by
  first | exact @GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar | exact GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar | (intros; apply GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar <;> assumption)
