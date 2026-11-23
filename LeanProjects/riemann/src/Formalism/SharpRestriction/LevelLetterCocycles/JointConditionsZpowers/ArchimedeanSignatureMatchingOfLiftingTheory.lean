import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.WachRestrictionOfLiftingPackage
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem delta_input_one_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.ElementDenominator.adm1 D HW F Cm := by
  unfold Formalism.MainNotions.ElementDenominator.adm1
  exact Formalism.MainNotions.DeltaInvariantLattices.thm1used_of (theorem_one_of_local_package D HW F Cm h56)

theorem delta_input_two_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.ElementDenominator.adm2 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm2
  exact proposition_two_of_local_package D HW F Cm h56

theorem delta_input_three_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.ElementDenominator.adm3 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm3
  exact lemma_three_of_local_package D HW F Cm h56

theorem archimedean_signature_matching_of_liftingTheory (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA : ℝ) (CB : ℝ) (CK : ℝ) (C : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching D HW F CA CB CK := by
  unfold Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching
  exact lift_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_five_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm5 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm5
  exact wach_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_six_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm6 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm6
  exact lifting_local_of_package D HW F C CA CB CK h54

theorem bloch_kato_input_of_dropping (D : D7)
    (hconds5 : Formalism.MainNotions.LocalSituation.Conclusion5 D) :
    Formalism.MainNotions.ElementDenominator.adm13 D := by
  unfold Formalism.MainNotions.ElementDenominator.adm13
  exact hconds5

end Formalism.MainNotions.N
