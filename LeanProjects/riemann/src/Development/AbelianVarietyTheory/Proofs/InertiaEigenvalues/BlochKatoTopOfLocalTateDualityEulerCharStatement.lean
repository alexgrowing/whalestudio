import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoTopOfLocalTateDualityEulerChar
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoTop_of_localTateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), tableLineDegreeTwo.aux₃ D HW F := by
  first | exact @GlobalTheory.TopClosing.blochKatoTop_of_localTateDuality_eulerChar_alt | exact GlobalTheory.TopClosing.blochKatoTop_of_localTateDuality_eulerChar_alt | (intros; apply GlobalTheory.TopClosing.blochKatoTop_of_localTateDuality_eulerChar_alt <;> assumption)
