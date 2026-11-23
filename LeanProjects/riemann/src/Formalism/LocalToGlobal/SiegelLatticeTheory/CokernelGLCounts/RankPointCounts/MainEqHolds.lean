import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClassHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlInvHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.StepPinExistsHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThmBChainG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataChoiceLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvHoldsGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UniformDenominatorExpansionLocal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NGLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf

theorem normExpDegC_holds : NormExpDegC :=
  normExpDegC_of_leaves Formalism.L2.SG.Closed.FinLeviC_holds Formalism.L2.SG.Closed.OOLintSumC_holds

theorem stepPointsG_holds : StepPointsG :=
  Formalism.L2.SG.Pf.MainEqPoints.stepPointsG_of_leaves Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds
    Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
    Formalism.L2.SG.NonRelPf.nonRelCharC_holds (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')

theorem stepNormOneG_holds : StepNormOneG :=
  Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen.stepNormOneG_of_leaves Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds
    Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
    Formalism.L2.SG.NonRelPf.nonRelCharC_holds (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')

theorem rowMainEqC_of_open (hNI : Formalism.L2.SG.NGCut.NormalInvariants.Gen.NmlInvG) (hB : StepChoiceConstantsC) (hE : StepPinExists)
    (hF : Formalism.L2.SG.Pf.FormRel.FormRelC) (hL : Formalism.L2.SG.Pf.MainEqLoc.StepLocPinnedG)
    (hT : Formalism.L2.SG.Pf.BDat.StepThmBG) : RowMainEqC :=
  rowMainEqC_of_pinned Formalism.FourierDecayAlt.P.norm_chain stepClassG_holds
    (Formalism.L2.SG.NGCut.NormalInvariants.Gen.stepNormalsG_of hNI Formalism.L2.SG.NGCut.NormalCount.NormCount_holds stepNormOneG_holds)
    stepPointsG_holds stepNormOneG_holds (tieOfCtx_of Formalism.L2.SG.NGLeaves.nondegenerate_gram_tuple) hB hE
    (Formalism.L2.SG.Pf.MainEqVanish.stepTermVanishG_of_form (formGC_of_rel hF)) (stepLocGenPinnedG_of_loc hL)
    (stepThmBPinnedG_of_bdat hT)

theorem rowMainEqC_of_fam (hNL : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine) (hNI : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt)
    (hNS : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep) (hB : StepChoiceConstantsC) (hE : StepPinExists)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (hFam : Formalism.L2.SG.Pf.MainEqFam.StepFamG)
    (hT : Formalism.L2.SG.Pf.BDat.StepThmBG) : RowMainEqC :=
  rowMainEqC_of_open (nmlInvG_of hNL hNI hNS) hB hE formRelC_holds
    (stepLocPinnedG_of_fam (Formalism.L2.SG.NGLeaves.ranks_of_dictionary hDict) hFam) hT

theorem rowMainEquation_of_family (hB : StepChoiceConstantsC)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (hFam : Formalism.L2.SG.Pf.MainEqFam.StepFamG)
    (hT : Formalism.L2.SG.Pf.BDat.StepThmBG) : RowMainEqC :=
  rowMainEqC_of_fam Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine_holds Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds
    Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep_holds hB Formalism.L2.SG.Closed.StepPinExists_holds hDict hFam hT

theorem rowMainEqC_of_shared (hSW : PI.VolStabS.MassDataS.SWXS)
    (hPC : Formalism.L2.SG.NGAnalytic.MassDataLemmas.OnTied fun _ X _ _ u u' _ ψ => Formalism.L2.SG.LocVol.ProdConv X u u' ψ)
    (hInfG : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
      Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (hFam : Formalism.L2.SG.Pf.MainEqFam.StepFamG)
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hA : Formalism.L2.SG.Pf.BDat.AmpUnif)
    (hR : Formalism.L2.SG.Pf.ThmBChain.RowRestUnifR) : RowMainEqC :=
  rowMainEquation_of_family (choice_massData hSW hPC hInfG) hDict hFam (theoremB_generic_final hB3 hA hR)

theorem rowMainEqC_of_shared2 (hSW : PI.VolStabS.MassDataS.SWXS)
    (hInfG : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
      Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (hFam : Formalism.L2.SG.Pf.MainEqFam.StepFamG)
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hA : Formalism.L2.SG.Pf.BDat.AmpUnif)
    (hR : Formalism.L2.SG.Pf.ThmBChain.RowRestUnifR) : RowMainEqC :=
  rowMainEqC_of_shared hSW Formalism.L2.SG.Pf.ProdConvCut2.prodConv_onTied hInfG hDict hFam hB3 hA hR

end Formalism.L2.SG.Pf
