import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericRowFamilyStepOfLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
open GlobalTheory.SnFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericRow_familyStep_of_leaves : (∀ D : Formalism.BasicNotions.D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) → Formalism.L2.SG.FamDefs.HTie → FamGen → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam → Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  first | exact @GlobalTheory.SnFam.Gen.stepFamG_of_fam | exact GlobalTheory.SnFam.Gen.stepFamG_of_fam | (intros; apply GlobalTheory.SnFam.Gen.stepFamG_of_fam <;> assumption)
