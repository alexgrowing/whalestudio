import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1f
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_corestriction_H1f : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LiftingTheory.adm20 D HW F := by
  first | exact @GlobalTheory.res_cor_H1f | exact GlobalTheory.res_cor_H1f | (intros; apply GlobalTheory.res_cor_H1f <;> assumption)
