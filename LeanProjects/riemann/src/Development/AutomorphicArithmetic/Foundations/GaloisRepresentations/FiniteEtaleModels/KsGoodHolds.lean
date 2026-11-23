import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovLink
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapFiniteEtaleSurjectiveStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.AdmissibleOfIntegralConjLe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepAHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiesAbsHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepBOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.TjExGOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BEtaPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ExistsIsoOfCart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsUnitNatOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ActGActGInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BLevOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BSecInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsDominantGenericFibre
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.KerAtLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OBaseOnto
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OStepF
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OLiftSys
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PDegGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFEtExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PNormExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PExtEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PBaseFet
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PQuotOf

namespace UpperTheory.Gal.FiniteEtaleModels

open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.CovMain UpperTheory.Gal.crystallineComparison.Mod

theorem stepA : StepA := stepA_holds (multUnit_of mIn) (latGen_of mIn) (clsEx_of mIn) (trEta_of mIn) (trBack_of mIn) (qComp_of mIn)

theorem baseFet : BaseFet := baseFet_holds (powCart_of mIn) (piFet_of mIn)

theorem stepB : StepB :=
  stepB_of (tjExG_of esNorm_link esGen_link objTri_holds pullIsog_holds pullKer_holds)
    (bRead_of (isogG_of (trEta_of mIn) (trBack_of mIn) (multUnit_of mIn) (trTj_of mIn)) (qObj_of mIn) (qComp_of mIn) objTri_holds)
    (bKer_of (secInjG_of pulledEx_holds pulledRead_holds pullKer_holds kerFromU_holds isoOfKer_holds) (trEtaPt_of mIn))
    (bLev_of latB_holds etaPtB_holds etInj_holds) (descExt_of normExt_holds) baseFet O.baseOnto pulledEx_holds

theorem quotOf : QuotOf := quotOf_holds (powCart_of mIn) (piInv_of mIn) (piFet_of mIn) (piSep_of mIn) (congCRT_of mIn) O.baseOnto

theorem extEx : ExtEx := extEx_holds mIn (powProj_of mIn)

theorem ksGood_holds : KSGood :=
  ksGood_of (siteEx_of mIn) (numEx_of mIn) (clsEx_of mIn) ksCover_holds (piInv_of mIn) (powCart_of mIn) extEx quotOf stepA stepB O.stepF
    degGen_holds fEtExt_holds liesAbs_holds

end UpperTheory.Gal.FiniteEtaleModels
