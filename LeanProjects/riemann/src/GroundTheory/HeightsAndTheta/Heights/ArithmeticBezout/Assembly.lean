import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerSectionOfConst
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectConstStep
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectConstZero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectAverage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerAverageSplit
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerIntegrand
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSphereMeanFubini
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PEvalSpecFirst
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleAverage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeAverage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFubini
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogAverage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogPointOf
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallAverageLinear
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSphereMeanLinearBall
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogMeasurable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreePos
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBallVolume
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAdmissibleAE
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAdmissibleAENrm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectSymm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleSectionData
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstHomog
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSupportCycleSection
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleIntegralSection
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormAssoc
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormCycleAdd
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormCycleSmul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleSectionChow
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstRename
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowCycleSwap
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstSwapMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProperSymmCycle
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerZeroSpec
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectPoint
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerSection
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.OfLeaves
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaInj
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaInjSet
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaLocal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBaseChangeAvoid
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartZeroTrdeg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormExtend
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormReducedRadical
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFiniteFibreDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeGraphCover
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeJacMeasurable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeKrullDimLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapAreaOne
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSmoothLocalGraph
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFormsThroughPoint
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGraphAreaFibre
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGraphAreaIntegral
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PHolomorphicImplicitGraph
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealNeBotDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealSeparate
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncidenceZeroLocus
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PKernelProjMeasurable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGenerators
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjPrimeHasPoint
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRadicalBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentGaussInvariant
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentJacComp
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentJacCompress
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughPointIncIdeal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughTwoPointsTrdeg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegAdjoinLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegBaseAlgebraic
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticImplicitChart
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchAwayFromRim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchContainsNormalPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchFillDimension
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInverseHolomorphic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInverseOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchLift
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchProperAtPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchesGoodPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchesToGoodPosition
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBrouwerFixedPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartChangeSheetNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSheetGramLintegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSliceSheetParam
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalFlatNotInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGeneralPointBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDominantFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteGermProjectionCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntSlice
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermFiniteProjection
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicIsolatedFibreOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImageDimLe
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicInverse
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInvarianceOfDomain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermComplementConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermRegularConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenFixed
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenPolyFull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCount
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCountPrime
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitAtBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitGoodPoints
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOnZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongMassNearSmall
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearNoetherNormalization
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalBranchedCovering
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalParametrisation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalTrace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogNormEnergyDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogNormGradDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PManifoldZerosComplementConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalComplementConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalGermIrreducible
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalLocallyIrreducible
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalMaximumPrinciple
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelProper
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalOpenMapping
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalRiemannExtension
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParametrisationSheetsConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPoincareLelong
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionInjectiveOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusIdentity
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetPieceProductAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetPieceReachesCentre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBandAbsEnergy
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBandEnergy
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutChain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutDecay
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceCutTailMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceFormLelong
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceFormLelongCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceFormMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLelongError
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLevelSet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLevelSetSmooth
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegCutTail
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegMassContinuous
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegMassLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegMassMono
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegTail
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegTailMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegVarBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceSectionTailMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceWeightBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceWeightMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOnChart
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepAreaCount
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepRankOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeEuclMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarIntChartChange
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarMassNearSmall
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.UnfoldingFormOfMatrix
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PConormalGenerationGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameGraphGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameImplicitGraph
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PJacobianRankGeneric
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ChowFormBaseChange.full : ChowFormBaseChange.Statement :=
  (ChowFormBaseChange.proof
    RadicalBaseChange.proof
    (ChowFormExtend.proof RadicalBaseChange.proof)
    (ChowFormReduced.proof_of_prime_separate
      IncIdealPrime.full
      (IncIdealSeparate.proof
        IncidenceZeroLocus.proof
        (FormsThroughPoint.proof
          IncidenceZeroLocus.proof
          ThroughPointIncIdeal.proof
          (ChartZeroTrdeg.proof AffineChartTrdeg.full)
          (ThroughTwoPointsTrdeg.proof TrdegAdjoinLe.proof)
          TrdegBaseAlgebraic.proof)
        (IncIdealNeBotDim.proof IncIdealDim.full))))

theorem BaseChangeAvoid.full : BaseChangeAvoid.Statement :=
  BaseChangeAvoid.proof

theorem ProjPrimeHasPoint.full : ProjPrimeHasPoint.Statement :=
  ProjPrimeHasPoint.proof

theorem ChowFormSectionVertical.full : ChowFormSectionVertical.Statement :=
  Vertical.ChowFormSectionVertical.full

theorem ConeMassOfFibre.full : ConeMassOfFibre.Statement :=
  (ConeMassOfFibre.of_open
    ConeFiniteFibreDim.proof
    (ConeGraphCover.proof
      ConeFiniteFibreDim.proof
      (ConeTangentDim.proof
        (ConeKrullDimLe.proof ConeFiniteFibreDim.proof)
        NullSmaller.full
        (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
      (ConeSmoothLocalGraph.proof PolyLocalGenerators.proof HolomorphicImplicitGraph.proof))
    (ConeJacMeasurable.proof TangentJacCompress.proof KernelProjMeasurable.proof)
    (ConeTangentDim.proof
      (ConeKrullDimLe.proof ConeFiniteFibreDim.proof)
      NullSmaller.full
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
    (GraphAreaFibre.proof
      (GraphAreaIntegral.proof GraphAreaHolomorphic.full)
      TangentJacComp.proof
      AreaMultiplicityWeight.proof)
    TangentGaussInvariant.proof)

theorem ConeIntegralMass.full : ConeIntegralMass.Statement :=
  (ConeIntegralMass.proof ConeFibreDegree.full ConeMassOfFibre.full)

theorem ConeBallFinite.full : ConeBallFinite.Statement :=
  (ConeBallFinite.proof ConeIntegralMass.full)

theorem ConeFsLogIntegrable.full : ConeFsLogIntegrable.Statement :=
  (ConeFsLogIntegrable.proof ConeBallFinite.full ConeSlabBound.full)

theorem ConeLogBound.full : ConeLogBound.Statement :=
  (ConeLogBound.of_leaves
    ConeIntegralMass.full
    ConeBallFinite.full
    ConeFsLogIntegrable.full
    ConeHyperplaneNull.full)

theorem BaseChangeLogBound.full : BaseChangeLogBound.Statement :=
  (BaseChangeLogBound.of_leaves
    ChowFormBaseChange.full
    BaseChangeAvoid.full
    ConeIntegralMass.full
    ConeBallFinite.full
    ConeFsLogIntegrable.full
    ConeHyperplaneNull.full)

theorem GreenSymmetry.of_remaining
    (hChowFormSectionAlgClosed : ChowFormSectionAlgClosed.Statement)
    (hSliceMassFinite : SliceMassFinite.Statement)
    (hChartChangeLocal : ChartChangeLocal.Statement)
    (hDivisorOneComponent : DivisorOneComponent.Statement)
    (hDivisorBranches : DivisorBranches.Statement)
    (hBranchIntDecompose : BranchIntDecompose.Statement)
    (hSliceBranchInt : SliceBranchInt.Statement)
    (hPolydiscLelongLimit : PolydiscLelongLimit.Statement)
    (hTwinComplexSetsNormalRiemannExtensionLocal : IndefiniteRowSideFullHecke.ComplexSets.NormalRiemannExtensionLocal.Statement)
    (hTwinComplexSetsIrreducibleGermProjectionOpenNear : IndefiniteRowSideFullHecke.ComplexSets.IrreducibleGermProjectionOpenNear.Statement)
    (hTwinComplexSetsProperOpenProjectionBranchLocus : IndefiniteRowSideFullHecke.ComplexSets.ProperOpenProjectionBranchLocus.Statement)
    (hTwinComplexSetsUnbranchedProperCountConstant : IndefiniteRowSideFullHecke.ComplexSets.UnbranchedProperCountConstant.Statement)
    (hTwinComplexSetsUnbranchedFibreSections : IndefiniteRowSideFullHecke.ComplexSets.UnbranchedFibreSections.Statement)
    (hTwinComplexSetsChangeOfVariablesDegree : IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree.Statement)
    (hTwinComplexSetsProperHolomorphicSurjective : IndefiniteRowSideFullHecke.ComplexSets.ProperHolomorphicSurjective.Statement)
    (hTwinComplexSetsHolomorphicKernelFibre : IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.Statement)
    (hTwinComplexSetsGenericProjectionFinite : IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.Statement)
    (hTwinComplexSetsLocalOrder : IndefiniteRowSideFullHecke.ComplexSets.LocalOrder.Statement)
    (hRegMassNearSmall : RegMassNearSmall.Statement)
    (hSliceFsLogIntegrable : SliceFsLogIntegrable.Statement)
    (hSliceTubeBandAbsEnergy : SliceTubeBandAbsEnergy.Statement) :
    GreenSymmetry.Statement := by
  have hComplexSetsLinearNoetherNormalization : ComplexSets.LinearNoetherNormalization.Statement :=
    ComplexSets.LinearNoetherNormalization.proof
  have hComplexSetsDiscriminantCover : ComplexSets.DiscriminantCover.Statement :=
    HilbertSamuel.Closed.ComplexSets.DiscriminantCover
  have hDiscriminantSheetCover : DiscriminantSheetCover.Statement :=
    DiscriminantSheetCover.proof hComplexSetsDiscriminantCover
  have hConeSliceSheetParam : ConeSliceSheetParam.Statement :=
    ConeSliceSheetParam.proof hDiscriminantSheetCover
  have hAreaFormulaLocal : AreaFormulaLocal.Statement :=
    AreaFormulaLocal.proof
  have hAreaFormulaInjSet : AreaFormulaInjSet.Statement :=
    AreaFormulaInjSet.proof hAreaFormulaLocal
  have hAreaFormulaInj : AreaFormulaInj.Statement :=
    AreaFormulaInj.proof hAreaFormulaInjSet
  have hConeMapAreaOne : ConeMapAreaOne.Statement :=
    ConeMapAreaOne.proof hAreaFormulaInj
  have hConeMapArea : ConeMapArea.Statement :=
    ConeMapArea.proof hConeMapAreaOne
  have hConeSheetGramLintegral : ConeSheetGramLintegral.Statement :=
    ConeSheetGramLintegral.proof hConeSliceSheetParam hConeMapArea
  have hSliceIdeal : SliceIdeal.Statement :=
    SliceIdeal.full
  have hSheetFormCompare : SheetFormCompare.Statement :=
    SheetFormCompare.proof
  have hSliceFormMass : SliceFormMass.Statement :=
    SliceFormMass.proof hSliceIdeal hSliceMassFinite hSheetFormCompare
  have hTwinComplexSetsFiniteMapOpen : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full
  have hTwinComplexSetsCriticalImageNull : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.full
  have hChartChangeSheetNull : ChartChangeSheetNull.Statement :=
    ChartChangeSheetNull.proof hTwinComplexSetsFiniteMapOpen hTwinComplexSetsCriticalImageNull
  have hVarIntChartChange : VarIntChartChange.Statement :=
    VarIntChartChange.proof hComplexSetsLinearNoetherNormalization hChartChangeSheetNull
      hChartChangeLocal
  have hFormIntSlice : FormIntSlice.Statement :=
    FormIntSlice.proof hSliceIdeal hSliceFormMass hVarIntChartChange
  have hSheetImageAreaSet : SheetImageAreaSet.Statement :=
    HilbertSamuel.Closed.SheetImageAreaSet
  have hLelongLimitOffZero : LelongLimitOffZero.Statement :=
    LelongLimitOffZero.of_open hSheetImageAreaSet
  have hDivisorGeneralPointBranches : DivisorGeneralPointBranches.Statement :=
    DivisorGeneralPointBranches.proof hDivisorOneComponent hDivisorBranches
  have hTwinComplexSetsNormalModelExists : IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof
  have hTwinComplexSetsNormalModelProper : IndefiniteRowSideFullHecke.ComplexSets.NormalModelProper.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalModelProper.proof
  have hTwinComplexSetsRiemannExtensionAnalytic : IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.proof
  have hTwinComplexSetsHolomorphicFibreInfinite : IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite.proof
  have hTwinComplexSetsBranchOffHypersurface : IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchOffHypersurface.proof hTwinComplexSetsHolomorphicFibreInfinite
  have hTwinComplexSetsVanishNearPoint : IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full
  have hJacobianRankGeneric : JacobianRankGeneric.Statement :=
    JacobianRankGeneric.proof
  have hConormalGenerationGeneric : ConormalGenerationGeneric.Statement :=
    ConormalGenerationGeneric.proof
  have hFrameJacobianGeneric : FrameJacobianGeneric.Statement :=
    FrameJacobianGeneric.proof hJacobianRankGeneric hConormalGenerationGeneric
  have hFrameImplicitGraph : FrameImplicitGraph.Statement :=
    FrameImplicitGraph.proof
  have hFrameGraphGeneric : FrameGraphGeneric.Statement :=
    FrameGraphGeneric.proof hFrameJacobianGeneric hFrameImplicitGraph
  have hTwinComplexSetsRegularOffHypersurface : IndefiniteRowSideFullHecke.ComplexSets.RegularOffHypersurface.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.RegularOffHypersurface.proof hFrameGraphGeneric
  have hTwinComplexSetsRegularLocusIdentity : IndefiniteRowSideFullHecke.ComplexSets.RegularLocusIdentity.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.RegularLocusIdentity.proof hTwinComplexSetsRegularOffHypersurface
  have hTwinComplexSetsNormalGermIrreducible : IndefiniteRowSideFullHecke.ComplexSets.NormalGermIrreducible.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalGermIrreducible.proof hTwinComplexSetsRegularLocusIdentity
      hTwinComplexSetsNormalRiemannExtensionLocal hTwinComplexSetsVanishNearPoint
  have hTwinComplexSetsAnalyticImplicitChart : IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.proof
  have hTwinComplexSetsRegularLocusDense : IndefiniteRowSideFullHecke.ComplexSets.RegularLocusDense.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.RegularLocusDense.proof hTwinComplexSetsAnalyticImplicitChart
  have hTwinComplexSetsGermFiniteProjection : IndefiniteRowSideFullHecke.ComplexSets.GermFiniteProjection.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.GermFiniteProjection.proof
  have hTwinComplexSetsProperOpenProjectionCover : IndefiniteRowSideFullHecke.ComplexSets.ProperOpenProjectionCover.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.ProperOpenProjectionCover.proof hTwinComplexSetsProperOpenProjectionBranchLocus
      hTwinComplexSetsUnbranchedProperCountConstant
  have hTwinComplexSetsFiniteGermProjectionCover : IndefiniteRowSideFullHecke.ComplexSets.FiniteGermProjectionCover.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.FiniteGermProjectionCover.proof
      hTwinComplexSetsIrreducibleGermProjectionOpenNear hTwinComplexSetsProperOpenProjectionCover
  have hTwinComplexSetsLocalParametrisation : IndefiniteRowSideFullHecke.ComplexSets.LocalParametrisation.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.LocalParametrisation.proof hTwinComplexSetsGermFiniteProjection
      hTwinComplexSetsFiniteGermProjectionCover
  have hTwinComplexSetsSheetPieceProductAnalytic : IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic.proof hTwinComplexSetsUnbranchedFibreSections
  have hTwinComplexSetsSheetPieceReachesCentre : IndefiniteRowSideFullHecke.ComplexSets.SheetPieceReachesCentre.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.SheetPieceReachesCentre.proof
  have hTwinComplexSetsParametrisationSheetsConnected : IndefiniteRowSideFullHecke.ComplexSets.ParametrisationSheetsConnected.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.ParametrisationSheetsConnected.proof hTwinComplexSetsSheetPieceProductAnalytic
      hTwinComplexSetsSheetPieceReachesCentre
  have hTwinComplexSetsIrreducibleGermRegularConnected : IndefiniteRowSideFullHecke.ComplexSets.IrreducibleGermRegularConnected.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.IrreducibleGermRegularConnected.proof hTwinComplexSetsLocalParametrisation
      hTwinComplexSetsParametrisationSheetsConnected
  have hTwinComplexSetsManifoldZerosComplementConnected : IndefiniteRowSideFullHecke.ComplexSets.ManifoldZerosComplementConnected.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.ManifoldZerosComplementConnected.proof
  have hTwinComplexSetsIrreducibleGermComplementConnected : IndefiniteRowSideFullHecke.ComplexSets.IrreducibleGermComplementConnected.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.IrreducibleGermComplementConnected.proof hTwinComplexSetsRegularLocusDense
      hTwinComplexSetsIrreducibleGermRegularConnected
      hTwinComplexSetsManifoldZerosComplementConnected
  have hTwinComplexSetsNormalComplementConnected : IndefiniteRowSideFullHecke.ComplexSets.NormalComplementConnected.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalComplementConnected.proof hTwinComplexSetsVanishNearPoint
      hTwinComplexSetsNormalGermIrreducible hTwinComplexSetsIrreducibleGermComplementConnected
  have hTwinComplexSetsNormalLocallyIrreducible : IndefiniteRowSideFullHecke.ComplexSets.NormalLocallyIrreducible.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalLocallyIrreducible.proof hTwinComplexSetsVanishNearPoint
      hTwinComplexSetsNormalComplementConnected
  have hTwinComplexSetsBrouwerFixedPoint : IndefiniteRowSideFullHecke.ComplexSets.BrouwerFixedPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BrouwerFixedPoint.proof hTwinComplexSetsChangeOfVariablesDegree
  have hTwinComplexSetsInvarianceOfDomain : IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain.proof hTwinComplexSetsBrouwerFixedPoint
  have hTwinComplexSetsInjectiveHolomorphicOpen : IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicOpen.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicOpen.proof hTwinComplexSetsInvarianceOfDomain
  have hTwinComplexSetsNormalModelOpenMapping : IndefiniteRowSideFullHecke.ComplexSets.NormalModelOpenMapping.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalModelOpenMapping.proof hTwinComplexSetsNormalLocallyIrreducible
      hTwinComplexSetsBranchOffHypersurface hTwinComplexSetsInjectiveHolomorphicOpen
  have hTwinComplexSetsBranchLift : IndefiniteRowSideFullHecke.ComplexSets.BranchLift.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchLift.proof hTwinComplexSetsRiemannExtensionAnalytic
      hTwinComplexSetsBranchOffHypersurface hTwinComplexSetsNormalModelOpenMapping
      hTwinComplexSetsNormalModelProper
  have hTwinComplexSetsBranchFillDimension : IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchFillDimension.proof hTwinComplexSetsHolomorphicFibreInfinite
  have hComplexSetsFibreBound : ComplexSets.FibreBound.Statement :=
    ComplexSets.FibreBound.full
  have hTwinComplexSetsHolomorphicIsolatedFibreOpen : IndefiniteRowSideFullHecke.ComplexSets.HolomorphicIsolatedFibreOpen.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.HolomorphicIsolatedFibreOpen.proof hTwinComplexSetsProperHolomorphicSurjective
  have hTwinComplexSetsNormalOpenMapping : IndefiniteRowSideFullHecke.ComplexSets.NormalOpenMapping.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalOpenMapping.proof hTwinComplexSetsNormalLocallyIrreducible
      hComplexSetsLinearNoetherNormalization hComplexSetsFibreBound hComplexSetsDiscriminantCover
      hTwinComplexSetsHolomorphicIsolatedFibreOpen
  have hTwinComplexSetsCriticalFlatNotInjective : IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof
  have hTwinComplexSetsInjectiveHolomorphicJacobianNeZero : IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof hTwinComplexSetsHolomorphicKernelFibre
      hTwinComplexSetsCriticalFlatNotInjective
  have hTwinComplexSetsInjectiveHolomorphicInverse : IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof
      hTwinComplexSetsInjectiveHolomorphicJacobianNeZero
  have hTwinComplexSetsProjectionInjectiveOffHypersurface : IndefiniteRowSideFullHecke.ComplexSets.ProjectionInjectiveOffHypersurface.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.ProjectionInjectiveOffHypersurface.proof_of_rank hJacobianRankGeneric
      hConormalGenerationGeneric
  have hTwinComplexSetsBranchInverseOffHypersurface : IndefiniteRowSideFullHecke.ComplexSets.BranchInverseOffHypersurface.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchInverseOffHypersurface.proof hTwinComplexSetsInjectiveHolomorphicInverse
      hTwinComplexSetsProjectionInjectiveOffHypersurface
  have hTwinComplexSetsNormalRiemannExtension : IndefiniteRowSideFullHecke.ComplexSets.NormalRiemannExtension.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalRiemannExtension.proof hTwinComplexSetsNormalRiemannExtensionLocal
      hTwinComplexSetsNormalLocallyIrreducible
  have hTwinComplexSetsBranchInverseHolomorphic : IndefiniteRowSideFullHecke.ComplexSets.BranchInverseHolomorphic.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchInverseHolomorphic.proof hTwinComplexSetsBranchFillDimension
      hTwinComplexSetsNormalOpenMapping hTwinComplexSetsBranchInverseOffHypersurface
      hTwinComplexSetsNormalRiemannExtension hTwinComplexSetsNormalLocallyIrreducible
  have hTwinComplexSetsIsolatedFibreOpen : IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpen.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric.proof hTwinComplexSetsGenericProjectionFinite
      hTwinComplexSetsFiniteMapOpen
  have hTwinComplexSetsLocalBranchedCovering : IndefiniteRowSideFullHecke.ComplexSets.LocalBranchedCovering.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.LocalBranchedCovering.proof hDiscriminantSheetCover
      hTwinComplexSetsIsolatedFibreOpen
  have hTwinComplexSetsLocalTrace : IndefiniteRowSideFullHecke.ComplexSets.LocalTrace.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.LocalTrace.proof hTwinComplexSetsLocalBranchedCovering
  have hTwinComplexSetsNormalMaximumPrinciple : IndefiniteRowSideFullHecke.ComplexSets.NormalMaximumPrinciple.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.NormalMaximumPrinciple.proof hTwinComplexSetsLocalTrace
  have hTwinComplexSetsBranchContainsNormalPoint : IndefiniteRowSideFullHecke.ComplexSets.BranchContainsNormalPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchContainsNormalPoint.proof hTwinComplexSetsNormalLocallyIrreducible
      hTwinComplexSetsBranchInverseHolomorphic hTwinComplexSetsNormalRiemannExtension
      hTwinComplexSetsNormalMaximumPrinciple
  have hTwinComplexSetsBranchAwayFromRim : IndefiniteRowSideFullHecke.ComplexSets.BranchAwayFromRim.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchAwayFromRim.proof hTwinComplexSetsNormalModelExists
      hTwinComplexSetsNormalModelProper hTwinComplexSetsBranchLift
      hTwinComplexSetsNormalLocallyIrreducible hTwinComplexSetsBranchContainsNormalPoint
  have hTwinComplexSetsBranchProperAtPoint : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.proof hTwinComplexSetsBranchAwayFromRim
  have hLelongLimitAtBranches : LelongLimitAtBranches.Statement :=
    LelongLimitAtBranches.proof hBranchIntDecompose hSliceBranchInt hPolydiscLelongLimit
      hTwinComplexSetsBranchProperAtPoint
  have hTwinComplexSetsGeneralProjection : IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.full
  have hTwinComplexSetsOneComponentGeneralPoint : IndefiniteRowSideFullHecke.ComplexSets.OneComponentGeneralPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.OneComponentGeneralPoint.full
  have hTwinComplexSetsSliceImmersiveGeneral : IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.full
  have hTwinComplexSetsBranchesGoodPoint : IndefiniteRowSideFullHecke.ComplexSets.BranchesGoodPoint.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchesGoodPoint.proof hTwinComplexSetsGeneralProjection
      hTwinComplexSetsOneComponentGeneralPoint hTwinComplexSetsSliceImmersiveGeneral
      hTwinComplexSetsBranchProperAtPoint
  have hTwinComplexSetsPowerUnitCount : IndefiniteRowSideFullHecke.ComplexSets.PowerUnitCount.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.PowerUnitCount.full
  have hTwinComplexSetsBranchesToGoodPosition : IndefiniteRowSideFullHecke.ComplexSets.BranchesToGoodPosition.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.BranchesToGoodPosition.proof hTwinComplexSetsBranchesGoodPoint
      hTwinComplexSetsPowerUnitCount
  have hLocalOrder : LocalOrder.Statement :=
    IndefiniteRowSideFullHecke.ComplexSets.LocalOrder.unfolding_form_of_matrix hTwinComplexSetsBranchesToGoodPosition
      hTwinComplexSetsLocalOrder
  have hLelongLimitGoodPoints : LelongLimitGoodPoints.Statement :=
    LelongLimitGoodPoints.proof hDivisorGeneralPointBranches hLelongLimitAtBranches hLocalOrder
  have hChartMassCompact : ChartMassCompact.Statement :=
    HilbertSamuel.Closed.ChartMassCompact
  have hVarMassNearSmall : VarMassNearSmall.Statement :=
    VarMassNearSmall.proof hChartMassCompact
  have hLelongMassNearSmall : LelongMassNearSmall.Statement :=
    LelongMassNearSmall.proof hRegMassNearSmall hVarMassNearSmall
  have hVarIntAdd : VarIntAdd.Statement :=
    VarIntAdd.of_open hSheetImageAreaSet
  have hLelongLimitOnZero : LelongLimitOnZero.Statement :=
    LelongLimitOnZero.proof hLelongLimitOffZero hLelongLimitGoodPoints hLelongMassNearSmall
      hVarIntAdd
  have hSliceBoundaryBound : SliceBoundaryBound.Statement :=
    SliceBoundaryBound.proof hChartMassCompact hSliceFormMass
  have hMaDensChain : MaDensChain.Statement :=
    MaDensChain.proof
  have hTubeCollarMass : TubeCollarMass.Statement :=
    HilbertSamuel.Closed.TubeCollarMass
  have hTubeDeepRankOne : TubeDeepRankOne.Statement :=
    TubeDeepRankOne.proof
  have hIsolatedFibreOpenPoly : IsolatedFibreOpenPoly.Statement :=
    IsolatedFibreOpenPoly.full
  have hComplexSetsGenericProjectionFinite : ComplexSets.GenericProjectionFinite.Statement :=
    ComplexSets.GenericProjectionFinite.full
  have hDominantFibreBound : DominantFibreBound.Statement :=
    DominantFibreBound.proof hComplexSetsGenericProjectionFinite
  have hImageDimLe : ImageDimLe.Statement :=
    ImageDimLe.proof
  have hIsolatedPointsCountPrime : IsolatedPointsCountPrime.Statement :=
    IsolatedPointsCountPrime.proof hIsolatedFibreOpenPoly hDominantFibreBound hImageDimLe
  have hIsolatedPointsCount : IsolatedPointsCount.Statement :=
    IsolatedPointsCount.proof hIsolatedPointsCountPrime
  have hTubeDeepAreaCount : TubeDeepAreaCount.Statement :=
    TubeDeepAreaCount.proof hIsolatedPointsCount
  have hTubeDeepWeightMass : TubeDeepWeightMass.Statement :=
    HilbertSamuel.Closed.TubeDeepWeightMass
  have hTubeDeepMass : TubeDeepMass.Statement :=
    TubeDeepMass.proof hTubeDeepRankOne hTubeDeepAreaCount hTubeDeepWeightMass
  have hTubeEuclMass : TubeEuclMass.Statement :=
    TubeEuclMass.proof hTubeCollarMass hTubeDeepMass
  have hCutOffLimit : CutOffLimit.Statement :=
    CutOffLimit.of_open hSheetImageAreaSet hTubeEuclMass
  have hStokesOnChart : StokesOnChart.Statement :=
    StokesOnChart.proof hComplexSetsDiscriminantCover hCutOffLimit
  have hLogNormGradDensNonneg : LogNormGradDensNonneg.Statement :=
    LogNormGradDensNonneg.proof
  have hSliceLevelSetSmooth : SliceLevelSetSmooth.Statement :=
    SliceLevelSetSmooth.proof hStokesOnChart hLogNormGradDensNonneg hMaDensChain hChartMassCompact
      hSliceMassFinite
  have hSliceLevelSet : SliceLevelSet.Statement :=
    SliceLevelSet.proof hSliceLevelSetSmooth
  have hSliceCutDecay : SliceCutDecay.Statement :=
    SliceCutDecay.proof hMaDensChain hSliceLevelSet hSliceMassFinite
  have hSliceComponents : SliceComponents.Statement :=
    SliceComponents.full
  have hSliceWeightMassFinite : SliceWeightMassFinite.Statement :=
    SliceWeightMassFinite.proof hSliceMassFinite
  have hStokesOnVariety : StokesOnVariety.Statement :=
    StokesOnVariety.of_open hSheetImageAreaSet hTubeEuclMass
  have hLogIntegrable : LogIntegrable.Statement :=
    LogIntegrable.of_open hSheetImageAreaSet
  have hLelongRegularise : LelongRegularise.Statement :=
    LelongRegularise.of_open hSheetImageAreaSet
  have hLelongLimit : LelongLimit.Statement :=
    LelongLimit.of_open hLelongLimitOnZero hSheetImageAreaSet
  have hPoincareLelong : PoincareLelong.Statement :=
    PoincareLelong.proof hStokesOnVariety hLelongRegularise hLelongLimit
  have hSliceFormLelongCompact : SliceFormLelongCompact.Statement :=
    SliceFormLelongCompact.proof hStokesOnVariety hLogIntegrable hPoincareLelong hChartMassCompact
      hSliceIdeal hSliceComponents
  have hSliceRegVarBound : SliceRegVarBound.Statement :=
    SliceRegVarBound.proof hSliceFormMass
  have hSliceRegMassMono : SliceRegMassMono.Statement :=
    SliceRegMassMono.proof hSliceFormMass
  have hSliceRegMassContinuous : SliceRegMassContinuous.Statement :=
    SliceRegMassContinuous.proof hSliceMassFinite hSheetFormCompare
  have hSliceCutOffLimit : SliceCutOffLimit.Statement :=
    SliceCutOffLimit.of_open hSheetFormCompare hSliceBoundaryBound hSliceCutDecay hSliceMassFinite
  have hSliceCutChain : SliceCutChain.Statement :=
    SliceCutChain.proof hChartMassCompact hLogIntegrable
  have hSliceLogIntegrable : SliceLogIntegrable.Statement :=
    SliceLogIntegrable.proof hSliceFsLogIntegrable
  have hSliceWeightBound : SliceWeightBound.Statement :=
    SliceWeightBound.proof hSliceLogIntegrable
  have hLogNormEnergyDensNonneg : LogNormEnergyDensNonneg.Statement :=
    LogNormEnergyDensNonneg.proof
  have hSliceBandAbsEnergy : SliceBandAbsEnergy.Statement :=
    SliceBandAbsEnergy.proof hLogIntegrable hLogNormEnergyDensNonneg hSliceTubeBandAbsEnergy
  have hSliceBandEnergy : SliceBandEnergy.Statement :=
    SliceBandEnergy.proof hLogIntegrable hLogNormEnergyDensNonneg hSliceBandAbsEnergy
  have hSliceLelongError : SliceLelongError.Statement :=
    SliceLelongError.proof hSliceCutChain hSliceWeightBound hSliceBandEnergy
  have hSliceSectionMass : SliceSectionMass.Statement :=
    SliceSectionMass.of_open hLelongLimitOnZero hSheetImageAreaSet hSliceLelongError
      hSliceMassFinite hTubeEuclMass
  have hSliceRegMassLimit : SliceRegMassLimit.Statement :=
    SliceRegMassLimit.proof hSliceCutOffLimit hStokesOnVariety hSliceFormLelongCompact
      hSliceSectionMass hSliceFormMass hChartMassCompact
  have hSliceSectionTailMass : SliceSectionTailMass.Statement :=
    SliceSectionTailMass.proof hSliceMassFinite
  have hSliceRegCutTail : SliceRegCutTail.Statement :=
    SliceRegCutTail.proof hSliceFormMass
  have hSliceCutTailMass : SliceCutTailMass.Statement :=
    SliceCutTailMass.proof hSliceMassFinite
  have hSliceRegTailMass : SliceRegTailMass.Statement :=
    SliceRegTailMass.proof hSliceRegMassMono hSliceRegMassContinuous hSliceRegMassLimit
      hSliceSectionTailMass hSliceRegCutTail hSliceCutTailMass
  have hSliceRegTail : SliceRegTail.Statement :=
    SliceRegTail.proof hSliceRegVarBound hSliceRegTailMass hSliceCutTailMass
  have hSliceFormLelong : SliceFormLelong.Statement :=
    SliceFormLelong.proof hSliceIdeal hSliceComponents hSliceWeightMassFinite
      hSliceFormLelongCompact hSliceRegTail
  have hGreenSymmetry : GreenSymmetry.Statement :=
    GreenSymmetry.of_open hChowFormSectionAlgClosed hComplexSetsLinearNoetherNormalization
      hConeSheetGramLintegral hFormIntSlice hLelongLimitOnZero hSheetFormCompare hSheetImageAreaSet
      hSliceBoundaryBound hSliceCutDecay hSliceFormLelong hSliceLelongError hSliceMassFinite
      hTubeEuclMass
  exact hGreenSymmetry

end GroundTheory.Heights₂.Heights
