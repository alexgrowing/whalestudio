import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowGen1POfSteps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLoc1OfFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmpQNotEqAmpG
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfGenericCorankOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamGen1
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepClass1Of
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOneIsEquivalenceNonzeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalMassLeGenericMassConstNine
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalNongenericBoundRecordFamily
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyRowWeightSumUnfoldingIdentityProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentLocalIdentityFamiliesLemmaH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqVanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem rowGen1P_of_siegelWeil_of_points : PI.VolStabS.MassDataS.SWXS → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine →
    Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep → StepPointsG → StepNormOneG → TieOfCtx →
    StepChoiceConstantsC → StepPinExists → GlobalTheory.SnPos.StepThmBGP → RowGen1P := by
  intro hSW hLine hInt hSep hPts hN1 hTie hCh hPin hThm
  have hEq : CorankOneIsEquivalenceOnRow := corankOne_isEquivalence_nonzeroGram_terms
  have hFam : FamGen1 := famGen1 hEq
  have hStepFam : StepFam1 :=
    stepFam1_of (fun D hk => GlobalTheory.localMass_le_genericMass_nine D.R.k D.R.rS hk) GlobalTheory.HTieLeaf.main hFam
      GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof (GlobalTheory.WeightsFamPf.weightsFam_of hSW) GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude GlobalTheory.SnFam.existFam
  have hLoc : StepLoc1 :=
    stepLoc1_of_fam (fun D => ((GlobalTheory.local_nongeneric_bound_record_family 39 le_rfl).2.1 D).1) hStepFam
  have hNml : StepNormals1 :=
    GlobalTheory.Core.One.stepNormals1_of hEq hLine hInt hSep Formalism.L2.SG.NGCut.NormalCount.NormCount_holds hN1
  have hVan : StepTermVanishG :=
    Formalism.L2.SG.Pf.MainEqVanish.stepTermVanishG_of_form (Formalism.L2.SG.Pf.formGC_of_rel Formalism.L2.SG.Pf.formRelC_holds)
  exact rowGen1P_of_steps Formalism.FourierDecayAlt.P.norm_chain (stepClass1_of hEq) hNml hPts hN1 hTie hCh hPin hVan hLoc hThm

end GlobalTheory.Core.One
