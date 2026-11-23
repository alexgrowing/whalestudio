import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyStepOfFourGlobalLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyStep_of_four_globalLeaves : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric → Formalism.L2.SG.FamDefs.ExistNG → Formalism.L2.SG.NGLocModel.StepFamC := by
  first | exact @GlobalTheory.stepFamC_of_globalLeaves | exact GlobalTheory.stepFamC_of_globalLeaves | (intros; apply GlobalTheory.stepFamC_of_globalLeaves <;> assumption)
