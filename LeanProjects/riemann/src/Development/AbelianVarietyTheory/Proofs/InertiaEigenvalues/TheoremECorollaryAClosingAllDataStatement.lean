import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremECorollaryAClosingAllData
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremE_corollaryA_closing_all_data : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∃ C₀ : ℝ, ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), WachCoordinates.Conclusion1 D 800 ∧ ∀ C₂ : ℝ, C₀ ≤ C₂ → WachCoordinates.Conclusion2 D C₂ := by
  first | exact @GlobalTheory.ThmECorA.closing | exact GlobalTheory.ThmECorA.closing | (intros; apply GlobalTheory.ThmECorA.closing <;> assumption)
