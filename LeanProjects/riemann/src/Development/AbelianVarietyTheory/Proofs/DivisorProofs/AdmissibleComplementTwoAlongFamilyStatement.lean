import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleComplementTwoAlongFamily
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleComplementTwo_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm → Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm := by
  first | exact @GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize | exact GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize | (intros; apply GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize <;> assumption)
