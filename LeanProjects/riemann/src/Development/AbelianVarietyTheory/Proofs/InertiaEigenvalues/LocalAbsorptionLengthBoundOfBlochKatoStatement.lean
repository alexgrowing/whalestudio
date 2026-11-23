import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalAbsorptionLengthBoundOfBlochKato
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_absorption_length_bound_of_blochKato : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), BlochKatoDuality.Conclusion1 D ∧ BlochKatoDuality.Conclusion2 D := by
  first | exact @GlobalTheory.ClosingStatement.main | exact GlobalTheory.ClosingStatement.main | (intros; apply GlobalTheory.ClosingStatement.main <;> assumption)
