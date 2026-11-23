import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundlePullbackVanish
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSubQuotient
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtNatCastOfAddOneLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IdealCycleSupportFinite
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVNumCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVertCutEff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivisorIdealCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Imports
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleEqZeroOfFormNotMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RelevantMinimalOfDivCycleNeZero
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExistsMultiHomogNotMemOfIsRelevant
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExceptionalDeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalAddOfFinite
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RatDiv
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtOfAddOneLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LtNatCastOfAddOneLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleLineBase
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmPairFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalCongrOnSupport
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem SymmetricSpanHsymm.full : SymmetricSpanHsymm.Statement := SymmetricSpanHsymm.proof

theorem DivisorIdealCycle.full : DivisorIdealCycle.Statement.{u} := DivisorIdealCycle.proof

theorem VNumCut.full : VNumCut.Statement.{u} := VNumCut.proof CutByForm.full

theorem VertCutEff.full : VertCutEff.Statement.{u} :=
  VertCutEff.proof VNumCut.full DivisorIdealCycle.full IntNumAddFirst.full

theorem LeftExpansion.full : LeftExpansion.Statement.{u} := LeftExpansion.proof VNumCut.full

theorem RightExpansion.full : RightExpansion.Statement.{u} :=
  RightExpansion.proof VertCutEff.full DivisorIdealCycle.full

theorem ExcessPositive.full : ExcessPositive.Statement.{u} := ExcessPositive.proof

theorem AvoidingFormExists.full : AvoidingFormExists.Statement.{u} := AvoidingFormExists.proof

theorem HorizontalAvoidingForm.full : HorizontalAvoidingForm.Statement.{u} :=
  HorizontalAvoidingForm.proof

theorem LeftSideAdditiveInDegree.full : LeftSideAdditiveInDegree.Statement.{u} := LeftSideAdditiveInDegree.proof

theorem RightSideMultiplicativeInForm.full : RightSideMultiplicativeInForm.Statement.{u} :=
  RightSideMultiplicativeInForm.proof DivCycleMul.full DivCycleFiniteSupport.full

theorem CommonFactorRemoval.full : CommonFactorRemoval.Statement.{u} := CommonFactorRemoval.proof DivCycleMul.full

theorem AdditivityInDivisor.full : AdditivityInDivisor.Statement.{u} :=
  AdditivityInDivisor.proof DivCycleMul.full DivCycleFiniteSupport.full IntNumAddFirst.full
    SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialIdealMultiHomog.full
    SpecialIdealCorresp.full SpecialQuotDim.full DimStrictDrop.full

theorem TautologicalCase.full : TautologicalCase.Statement.{u} :=
  TautologicalCase.proof IntNumAddFirst.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full
    SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full DimStrictDrop.full

theorem FlagBundlePullbackVanish.of_open (hdim : FlagBundleDim.Statement) :
    FlagBundlePullbackVanish.Statement :=
  FlagBundlePullbackVanish.proof FieldNumbers.ProjectionFormulaContracted.full hdim

theorem FlagBundleCut.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement) :
    FlagBundleCut.Statement :=
  FlagBundleCut.proof hdim hforms hdiv FieldNumbers.CutRational.full

theorem FlagBundleLineBase.of_open (hdim : FlagBundleDim.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : FlagBundleLineBase.Statement :=
  FlagBundleLineBase.proof hdim hsec hdeg
    (FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (FieldNumbers.DivPushForward.proof FieldNumbers.ContractRelDimLe.proof hloc))

theorem NumericalSegre.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : NumericalSegre.Statement :=
  NumericalSegre.proof FieldNumbers.IntNumAdd.full hdim (FlagBundleCut.of_open hdim hforms hdiv)
    (FlagBundlePullbackVanish.of_open hdim) (FlagBundleLineBase.of_open hdim hsec hdeg hloc)

theorem LocalCoefficient.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    LocalCoefficient.Statement.{u} :=
  LocalCoefficient.proof hl hr hring

theorem NoCommonComponentCase.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} :=
  NoCommonComponentCase.proof LeftExpansion.full RightExpansion.full (LocalCoefficient.of_open hl hr hring)
    IntNumVanish.full

theorem BlowUpModel.of_open (hrees : ReesAlgebraDim.Statement.{u}) : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof hrees

theorem BlowUpDecomposition.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) : BlowUpDecomposition.Statement.{u} :=
  BlowUpDecomposition.proof (BlowUpModel.of_open hrees) hst

theorem BlowUpInvariance.of_open (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpInvariance.Statement.{u} :=
  BlowUpInvariance.proof hvert hdiv hhor hcomp DivCycleFiniteSupport.full

theorem BlowUpReduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpReduction.Statement.{u} :=
  BlowUpReduction.proof (BlowUpDecomposition.of_open hrees hst)
    (BlowUpInvariance.of_open hvert hdiv hhor hcomp) CommonFactorRemoval.full AdditivityInDivisor.full
    RightSideMultiplicativeInForm.full LeftSideAdditiveInDegree.full TautologicalCase.full

theorem CommonFactorInduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hdrop : BlowUpExcessDecreases.Statement.{u})
    (hvert : BlowUpVerticalPush.Statement.{u}) (hdiv : BlowUpDivisorPush.Statement.{u})
    (hhor : BlowUpHorizontalCorresp.Statement.{u}) (hcomp : HorizontalComponentModel.Statement.{u}) :
    CommonFactorInduction.Statement.{u} :=
  CommonFactorInduction.proof ExcessPositive.full AvoidingFormExists.full HorizontalAvoidingForm.full
    (BlowUpDecomposition.of_open hrees hst) hdrop
    (BlowUpReduction.of_open hrees hst hvert hdiv hhor hcomp) LeftSideAdditiveInDegree.full RightSideMultiplicativeInForm.full
    DivCycleMul.full

theorem VerticalDivisorsCommute.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u})
    (hrees : ReesAlgebraDim.Statement.{u}) (hst : BlowUpStrictTransform.Statement.{u})
    (hdrop : BlowUpExcessDecreases.Statement.{u}) (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : VerticalDivisorsCommute.Statement.{u} :=
  VerticalDivisorsCommute.of_steps (NoCommonComponentCase.of_open hl hr hring)
    (CommonFactorInduction.of_open hrees hst hdrop hvert hdiv hhor hcomp)

theorem HsymmPairFlagIndependence.of_open (hC2 : VerticalDivisorsCommute.Statement.{0})
    (hclos : GenericProjClosureModel.Statement) (hseg : SegreClosureNumber.Statement) :
    HsymmPairFlagIndependence.Statement :=
  HsymmPairFlagIndependence.proof (PairNumberExpansionIndependence.proof hC2) hclos hseg

theorem FlagIndependence.of_open (hC2 : VerticalDivisorsCommute.Statement.{0})
    (hclos : GenericProjClosureModel.Statement) (hseg : SegreClosureNumber.Statement) :
    FlagIndependence.Statement :=
  FlagIndependence.proof (PairNumberExpansionIndependence.proof hC2)
    (HsymmPairFlagIndependence.of_open hC2 hclos hseg) SymmetricSpanHsymm.full

theorem PairCocycle.of_open (hC2 : VerticalDivisorsCommute.Statement.{0})
    (hclos : GenericProjClosureModel.Statement) (hseg : SegreClosureNumber.Statement) :
    PairCocycle.Statement :=
  PairCocycle.proof (FlagIndependence.of_open hC2 hclos hseg) hC2 IntNumAddFirst.full

theorem SubQuotient.of_open (hC2 : VerticalDivisorsCommute.Statement.{0})
    (hclos : GenericProjClosureModel.Statement) (hseg : SegreClosureNumber.Statement) :
    SubQuotient.Statement :=
  SubQuotient.proof (FlagIndependence.of_open hC2 hclos hseg)

theorem ScalarQuotient.of_open (hC2 : VerticalDivisorsCommute.Statement.{0})
    (hclos : GenericProjClosureModel.Statement) (hseg : SegreClosureNumber.Statement) :
    ScalarQuotient.Statement :=
  ScalarQuotient.proof (FlagIndependence.of_open hC2 hclos hseg)

end GroundTheory.Heights₂.Heights.NumbersDVR
