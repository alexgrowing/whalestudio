import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBridge
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.AevalNeZeroOfNotMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZIff
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.Intersections.LiftZComponent
import GroundTheory.HeightsAndTheta.Heights.Intersections.AevalMemAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsNormalise
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogProdInt
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
import GroundTheory.HeightsAndTheta.Heights.Intersections.PullWMemFibre
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.Intersections.DetRestrictScalarsEqZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.NormSegreSameOrbit
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsSheetPullW
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogOfPullWeight
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsRest
import GroundTheory.HeightsAndTheta.Heights.Intersections.ChartCongr
import GroundTheory.HeightsAndTheta.Heights.Intersections.PAPrime
import GroundTheory.HeightsAndTheta.Heights.Intersections.PAdjoinIndepRelfinrank
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBCMult
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBaseChange
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBaseRatioBasis
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PCentreOverW
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartDetRatio
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartDualRational
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartFormsRational
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartScalingIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChoice
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDeLeSemiPos
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDeSlotAdd
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDegrees
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagDiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagFormDiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagForms
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOffFrame
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOffMinor
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOffUnit
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrd
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrdOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagPull
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagPullI
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagRatioBasis
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagRelevant
import GroundTheory.HeightsAndTheta.Heights.Intersections.PEvalKerKrullDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreIsolFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreOverFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreProduct
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFinrankAdjoinRange
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagFibre
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagMinorsBaseChange
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagMinorsTrdeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagMultiHomog
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagPivotAlgIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagPivotIdentity
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFnDegAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PHorizNotMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.PIntClosureLocFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLinEmbed
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHomogeneousOfIsMultiHomogOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLinearQuotient
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingChartLoc
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingInj
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingIntClosure
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.PMobiusAlgIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.POrbitCompNonvanish
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.PrimePairSetFirst
import GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreBij
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreMult
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFSecRed
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFStep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsSide
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTail
import GroundTheory.HeightsAndTheta.Heights.Intersections.DeEqZeroOfSemiPosOff
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleFibre
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleMultiHomog
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsMeasurable
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAddFirst
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsMonoSemiPos
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsRegLimit
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.LeOfHeightMapEqZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotMemOfNonZeroDivisor
import GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldLeLocRing
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisTer
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProofOfNoethPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.LogCardLocIdealUnitMul
import GroundTheory.HeightsAndTheta.Heights.Intersections.LogNormDivSameOrbit
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIsSheetFinZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisMore
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisFurther
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisExtra
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisRest
import GroundTheory.HeightsAndTheta.Heights.Intersections.IntCastMemRegMaxAt
import GroundTheory.HeightsAndTheta.Heights.Intersections.OrderOfIntegral
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisSide
import GroundTheory.HeightsAndTheta.Heights.Intersections.CardLeRingKrullDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.KerIsMultiHomogIdeal
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisTail
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisLast
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArIntMul
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRSlotAdd
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRankAdjoinFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRankFracDegree
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRelAlgClosureFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRelBaseChange
import GroundTheory.HeightsAndTheta.Heights.Intersections.PResExists
import GroundTheory.HeightsAndTheta.Heights.Intersections.UnitChartOperator
import GroundTheory.HeightsAndTheta.Heights.Intersections.FourierIntegralBound
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocChartRatio
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocIntegral
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocLength
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocLengthSum
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRank
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRankAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRankFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSheetHessPSD
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSwapCycles
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIExists
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIMultilin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmISymm
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTrdegAdjoinFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.PValCentreZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.PWWArithVar
import GroundTheory.HeightsAndTheta.Heights.Intersections.PWWRatioBasis
import GroundTheory.HeightsAndTheta.Heights.Intersections.PWellDefined
import GroundTheory.HeightsAndTheta.Heights.Intersections.PYYRatioBasis
import GroundTheory.HeightsAndTheta.Heights.Intersections.PZIntAdd
import GroundTheory.HeightsAndTheta.Heights.Intersections.PZIntPoint
import GroundTheory.HeightsAndTheta.Heights.Intersections.PZeroSetNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChange
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Contract
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixed
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Multilin
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordFibreDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordRatioDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFCoord
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.OfGenDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreMultiHomog
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGenFibreChartDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSymmRelabel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterHironaka
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

theorem RegularityFunctionFieldNumber.full : GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.proof

theorem RegularityDivisorSupportClosed.full : GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.proof

theorem LocRingPow.full : GroundTheory.Heights₂.Heights.Inter.LocRingPow.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingPow.proof

theorem RegularityDenominator.full : GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.proof GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.full GroundTheory.Heights₂.Heights.Inter.LocRingPow.full

theorem RegularityValuationCentre.full : GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre.proof

theorem RegularityRelativeClosedPoint.full : GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint.proof

theorem RegularityIntegral.full : GroundTheory.Heights₂.Heights.Inter.RegularityIntegral.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityIntegral.proof GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre.full GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint.full

theorem RegularityOrder.full : GroundTheory.Heights₂.Heights.Inter.RegularityOrder.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityOrder.proof GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.full GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.full GroundTheory.Heights₂.Heights.Inter.RegularityIntegral.full

theorem RegularityLocalPrime.full : GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full

theorem RegularityLocalize.full : GroundTheory.Heights₂.Heights.Inter.RegularityLocalize.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalize.proof GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.full

theorem regularityLocalDimension_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityLocalDimension_holds

theorem RegularityLocalFinite.full : GroundTheory.Heights₂.Heights.Inter.RegularityLocalFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalFinite.proof GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.full

theorem LocRingNoeth.full : GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.LocRingNoeth

theorem pointForm_holds.full : GroundTheory.Heights₂.Heights.Inter.pointForm_holds.Statement :=
  GroundTheory.Heights₂.Heights.Targets.Contract.pulledBackForms_topDensity_vanish

theorem PullbackEliminationOfVariable.full : GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.proof

theorem PullbackVanishingOfNullCycle.full : GroundTheory.Heights₂.Heights.Inter.PullbackVanishingOfNullCycle.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PullbackVanishingOfNullCycle.proof GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.full

theorem DiagForms.full : GroundTheory.Heights₂.Heights.Inter.DiagForms.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagForms.proof

theorem DiagOffFrame.full : GroundTheory.Heights₂.Heights.Inter.DiagOffFrame.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagOffFrame.proof

theorem DiagOffMinor.full : GroundTheory.Heights₂.Heights.Inter.DiagOffMinor.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagOffMinor.proof

theorem DiagOffUnit.full : GroundTheory.Heights₂.Heights.Inter.DiagOffUnit.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagOffUnit.proof GroundTheory.Heights₂.Heights.Inter.DiagOffFrame.full GroundTheory.Heights₂.Heights.Inter.DiagOffMinor.full

theorem ChartFormsRational.full : GroundTheory.Heights₂.Heights.Inter.ChartFormsRational.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ChartFormsRational.proof

theorem DiagFormDiv.full : GroundTheory.Heights₂.Heights.Inter.DiagFormDiv.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagFormDiv.proof GroundTheory.Heights₂.Heights.Inter.ChartFormsRational.full

theorem DiagOrdOne.full : GroundTheory.Heights₂.Heights.Inter.DiagOrdOne.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagOrdOne.proof GroundTheory.Heights₂.Heights.Inter.DiagFormDiv.full

theorem DiagRelevant.full : GroundTheory.Heights₂.Heights.Inter.DiagRelevant.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagRelevant.proof

theorem DiagOrd.full : GroundTheory.Heights₂.Heights.Inter.DiagOrd.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagOrd.proof GroundTheory.Heights₂.Heights.Inter.DiagOffUnit.full GroundTheory.Heights₂.Heights.Inter.DiagOrdOne.full GroundTheory.Heights₂.Heights.Inter.DiagRelevant.full

theorem DiagDiv.full : GroundTheory.Heights₂.Heights.Inter.DiagDiv.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagDiv.proof GroundTheory.Heights₂.Heights.Inter.DiagForms.full GroundTheory.Heights₂.Heights.Inter.DiagOrd.full

theorem RankAdjoinFrac.full : GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac.proof

theorem regularityEmbedding_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.proof

theorem ProjectivePointVertical.full : GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.proof (by intros; exact GroundTheory.Heights₂.Heights.geoNumStatement _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ProjContract.full _ _ _ _ _)

theorem PushforwardProjectivePoint.full : GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.proof GroundTheory.Heights₂.Heights.imageArith GroundTheory.Heights₂.Heights.Inter.pointForm_holds.full GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.full

theorem ArithmeticIntersectionHorizontal.full : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal.proof ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith GroundTheory.Heights₂.Heights.imageArith GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.full

theorem ArithmeticIntersectionFibreMultiHomogeneous.full : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionFibreMultiHomogeneous.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionFibreMultiHomogeneous.proof

theorem EvalKerKrullDim.full : GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.Statement :=
  GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.proof

theorem FibreTranscendenceDegreeAlt.full : GroundTheory.Heights₂.Heights.Inter.FibreTranscendenceDegreeAlt.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreTranscendenceDegreeAlt.proof GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.full

theorem FibreDimensionZero.full : GroundTheory.Heights₂.Heights.Inter.FibreDimensionZero.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreDimensionZero.proof GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionFibreMultiHomogeneous.full GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.full GroundTheory.Heights₂.Heights.Inter.FibreTranscendenceDegreeAlt.full

theorem ChartRankAdjoin.full : GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.proof

theorem FnDegAdjoin.full : GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin.proof

theorem ChartScalingIndep.full : GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.proof

theorem AdjoinIndepRelfinrank.full : GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.Statement :=
  GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.proof

theorem FinrankAdjoinRange.full : GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.proof

theorem VerticalDegreeAfterAdjoining.full : GroundTheory.Heights₂.Heights.Inter.VerticalDegreeAfterAdjoining.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalDegreeAfterAdjoining.proof GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac.full GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin.full GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.full GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.full GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.full

theorem VerticalDegree.full : GroundTheory.Heights₂.Heights.Inter.VerticalDegree.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalDegree.proof GroundTheory.Heights₂.Heights.Inter.FibreDimensionZero.full GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.full GroundTheory.Heights₂.Heights.Inter.VerticalDegreeAfterAdjoining.full

theorem Conservation.full : GroundTheory.Heights₂.Heights.Inter.Conservation.Statement :=
  GroundTheory.Heights₂.Heights.Inter.Conservation.proof

theorem ValCentreZ.full : GroundTheory.Heights₂.Heights.Inter.ValCentreZ.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ValCentreZ.proof

theorem CentreOverW.full : GroundTheory.Heights₂.Heights.Inter.CentreOverW.Statement :=
  GroundTheory.Heights₂.Heights.Inter.CentreOverW.proof

theorem SemilocIntegral.full : GroundTheory.Heights₂.Heights.Inter.SemilocIntegral.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocIntegral.proof GroundTheory.Heights₂.Heights.Inter.ValCentreZ.full GroundTheory.Heights₂.Heights.Inter.CentreOverW.full

theorem LocRingChartLoc.full : GroundTheory.Heights₂.Heights.Inter.LocRingChartLoc.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingChartLoc.proof

theorem RelAlgClosureFinite.full : GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.proof

theorem IntClosureLocFinite.full : GroundTheory.Heights₂.Heights.Inter.IntClosureLocFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.IntClosureLocFinite.proof GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.full

theorem LocRingIntClosureFinite.full : GroundTheory.Heights₂.Heights.Inter.LocRingIntClosureFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingIntClosureFinite.proof GroundTheory.Heights₂.Heights.Inter.LocRingChartLoc.full GroundTheory.Heights₂.Heights.Inter.IntClosureLocFinite.full

theorem LocRingFrac.full : GroundTheory.Heights₂.Heights.Inter.LocRingFrac.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingFrac.proof

theorem LocRingLocal.full : GroundTheory.Heights₂.Heights.Inter.LocRingLocal.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.LocRingLocal

theorem LocRingDimOne.full : GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.proof GroundTheory.Heights₂.Heights.Inter.LocRingFrac.full GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.full GroundTheory.Heights₂.Heights.Inter.LocRingLocal.full GroundTheory.Heights₂.Heights.Inter.LocRingPow.full

theorem SemilocFinite.full : GroundTheory.Heights₂.Heights.Inter.SemilocFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocFinite.proof GroundTheory.Heights₂.Heights.Inter.SemilocIntegral.full GroundTheory.Heights₂.Heights.Inter.LocRingIntClosureFinite.full GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.full

theorem LocRingInj.full : GroundTheory.Heights₂.Heights.Inter.LocRingInj.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingInj.proof

theorem RatioAlgDep.full : GroundTheory.Heights₂.Heights.Inter.RatioAlgDep.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RatioAlgDep.proof

theorem MobiusAlgIndep.full : GroundTheory.Heights₂.Heights.Inter.MobiusAlgIndep.Statement :=
  GroundTheory.Heights₂.Heights.Inter.MobiusAlgIndep.proof

theorem YYRatioBasis.full : GroundTheory.Heights₂.Heights.Inter.YYRatioBasis.Statement :=
  GroundTheory.Heights₂.Heights.Inter.YYRatioBasis.proof GroundTheory.Heights₂.Heights.Inter.MobiusAlgIndep.full

theorem regularityDehomogenization_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityDehomogenization_holds

theorem GenericPointExists.full : GroundTheory.Heights₂.Heights.Inter.GenericPointExists.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointExists.proof

theorem pointFormEuler_holds.full : GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds.proof

theorem DiagPull.full : GroundTheory.Heights₂.Heights.Inter.DiagPull.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagPull.proof

theorem DiagPullI.full : GroundTheory.Heights₂.Heights.Inter.DiagPullI.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagPullI.proof GroundTheory.Heights₂.Heights.Inter.DiagDiv.full GroundTheory.Heights₂.Heights.Inter.DiagPull.full

theorem ZeroSetNull.full : GroundTheory.Heights₂.Heights.Inter.ZeroSetNull.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ZeroSetNull.proof

theorem ThmIUnique.full : GroundTheory.Heights₂.Heights.Inter.ThmIUnique.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ThmIUnique.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero

theorem BlockRatioAlg.full : GroundTheory.Heights₂.Heights.Inter.BlockRatioAlg.Statement :=
  GroundTheory.Heights₂.Heights.Inter.BlockRatioAlg.proof

theorem BaseRatioBasis.full : GroundTheory.Heights₂.Heights.Inter.BaseRatioBasis.Statement :=
  GroundTheory.Heights₂.Heights.Inter.BaseRatioBasis.proof

theorem ChartDetRatio.full : GroundTheory.Heights₂.Heights.Inter.ChartDetRatio.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ChartDetRatio.proof

theorem ChartDualRational.full : GroundTheory.Heights₂.Heights.Inter.ChartDualRational.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ChartDualRational.proof

theorem WWRatioBasis.full : GroundTheory.Heights₂.Heights.Inter.WWRatioBasis.Statement :=
  GroundTheory.Heights₂.Heights.Inter.WWRatioBasis.proof GroundTheory.Heights₂.Heights.Inter.MobiusAlgIndep.full

theorem DiagRatioBasis.full : GroundTheory.Heights₂.Heights.Inter.DiagRatioBasis.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagRatioBasis.proof GroundTheory.Heights₂.Heights.Inter.YYRatioBasis.full

theorem WWArithVar.full : GroundTheory.Heights₂.Heights.Inter.WWArithVar.Statement :=
  GroundTheory.Heights₂.Heights.Inter.WWArithVar.proof GroundTheory.Heights₂.Heights.Inter.BaseRatioBasis.full GroundTheory.Heights₂.Heights.Inter.ChartDetRatio.full GroundTheory.Heights₂.Heights.Inter.ChartDualRational.full GroundTheory.Heights₂.Heights.Inter.YYRatioBasis.full GroundTheory.Heights₂.Heights.Inter.WWRatioBasis.full GroundTheory.Heights₂.Heights.Inter.DiagRatioBasis.full

theorem FibreProduct.full : GroundTheory.Heights₂.Heights.Inter.FibreProduct.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreProduct.proof GroundTheory.Heights₂.Heights.Inter.WWArithVar.full GroundTheory.Heights₂.Heights.Inter.DiagDiv.full GroundTheory.Heights₂.Heights.Inter.DiagPull.full

theorem InductiveIntersectionFormula.full : GroundTheory.Heights₂.Heights.Inter.InductiveIntersectionFormula.Statement :=
  GroundTheory.Heights₂.Heights.Inter.InductiveIntersectionFormula.proof

theorem ArithmeticIntersectionChartFinite.full : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionChartFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionChartFinite.proof

theorem pullbackBadImage_holds.full : GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.proof

theorem FibreLocal.full : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreLocal.proof

theorem SpecIntHeightFormula.full : GroundTheory.Heights₂.Heights.Inter.SpecIntHeightFormula.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SpecIntHeightFormula.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero

theorem Choice.full : GroundTheory.Heights₂.Heights.Inter.Choice.Statement :=
  GroundTheory.Heights₂.Heights.Inter.Choice.proof

theorem Closed.IndefiniteRowSideFullHecke.ZIntPoint : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ZIntPoint.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ZIntPoint.proof

theorem PFFibreMult.full : GroundTheory.Heights₂.Heights.Inter.PFFibreMult.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PFFibreMult.proof

theorem regularityLocalCardinality_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityLocalCardinality_holds

theorem PFHoriz.full : GroundTheory.Heights₂.Heights.Inter.PFHoriz.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PFHoriz.proof

theorem pullbackPushforward_holds.full : GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.pullbackPushforward_holds

theorem LinearQuotient.full : GroundTheory.Heights₂.Heights.Inter.LinearQuotient.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LinearQuotient.proof

theorem LineFibreBlocks.full : GroundTheory.Heights₂.Heights.Inter.LineFibreBlocks.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LineFibreBlocks.proof GroundTheory.Heights₂.Heights.Inter.LinearQuotient.full

theorem regularityLocalFlat_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.proof

theorem pointFormRank_holds.full : GroundTheory.Heights₂.Heights.Inter.pointFormRank_holds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.pointFormRank_holds

theorem PFIntZero.full : GroundTheory.Heights₂.Heights.Inter.PFIntZero.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.PFIntZero

theorem ArithmeticIntersectionFifth.full : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionFifth.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionFifth.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero

theorem BlockGenFinite.full : GroundTheory.Heights₂.Heights.Inter.BlockGenFinite.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.BlockGenFinite

theorem SemiPosTwist.full : GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.SemiPosTwist

theorem ArithmeticIntersectionSecond.full : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionSecond.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionSecond.proof

theorem RankFracDegree.full : GroundTheory.Heights₂.Heights.Inter.RankFracDegree.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RankFracDegree.proof

theorem regularityPointsSum_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.proof

theorem HorizNotMem.full : GroundTheory.Heights₂.Heights.Inter.HorizNotMem.Statement :=
  GroundTheory.Heights₂.Heights.Inter.HorizNotMem.proof

theorem SheetHessPSD.full : GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.proof

theorem RegCurvBound.full : GroundTheory.Heights₂.Heights.Inter.RegCurvBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.RegCurvBound

theorem TorusInvLevi.full : GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.Statement :=
  GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.proof

theorem OrbitCompNonvanish.full : GroundTheory.Heights₂.Heights.Inter.OrbitCompNonvanish.Statement :=
  GroundTheory.Heights₂.Heights.Inter.OrbitCompNonvanish.proof

theorem regularityLocalResidue_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds.proof

theorem PFVert.full : GroundTheory.Heights₂.Heights.Inter.PFVert.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PFVert.proof (by intros; exact GroundTheory.Heights₂.Heights.geoNumStatement _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _) GroundTheory.Heights₂.Heights.Targets.contractMixedField

theorem RegularityAdditive.full : GroundTheory.Heights₂.Heights.Inter.RegularityAdditive.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityAdditive.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite

theorem FibreIsolFinite.full : GroundTheory.Heights₂.Heights.Inter.FibreIsolFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreIsolFinite.proof

theorem PFFibreBij.full : GroundTheory.Heights₂.Heights.Inter.PFFibreBij.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PFFibreBij.proof

theorem pullbackDensity_holds.full : GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.proof

theorem Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.Contract : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractStatement :=
  GroundTheory.Heights₂.Heights.Targets.Contract.of_found GroundTheory.Heights₂.Heights.imageArith GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.full

theorem Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixed : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedStatement :=
  GroundTheory.Heights₂.Heights.Targets.ContractMixed.of_found GroundTheory.Heights₂.Heights.imageArith GroundTheory.Heights₂.Heights.Inter.pointForm_holds.full GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.full GroundTheory.Heights₂.Heights.Inter.PFIntZero.full GroundTheory.Heights₂.Heights.Inter.PFVert.full

theorem Closed.ReciprocityTheory.ChartRestriction.G.AI.I2.Unique : ReciprocityTheory.ChartRestriction.G.AI.I2.UniqueStatement :=
  GroundTheory.Heights₂.Heights.Inter.ThmIUnique.full

theorem Closed.ReciprocityTheory.ChartRestriction.G.AI.I2.Conservation : ReciprocityTheory.ChartRestriction.G.AI.I2.ConservationStatement :=
  GroundTheory.Heights₂.Heights.Inter.Conservation.full

theorem Closed.Targets.GenFibreChartDeg : GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.Statement :=
  GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.proof GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.full GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.full

theorem Closed.Targets.CoordFibreDeg : GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.Statement :=
  GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.proof GroundTheory.Heights₂.Heights.Targets.FibreMultiHomog.proof GroundTheory.Heights₂.Heights.Inter.Closed.Targets.GenFibreChartDeg GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg.proof

theorem RatR.of_remaining
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.RatR.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RatR.proof hPtsIntegrable

theorem ArithmeticIntersectionVertical.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι') :
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionVertical.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionVertical.proof (by intros; exact GroundTheory.Heights₂.Heights.geoNumStatement _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ProjContract.full _ _ _ _ _) hProjDeg GroundTheory.Heights₂.Heights.Inter.VerticalDegree.full

theorem FibreOverFinite.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.proof hFibreIncomp

theorem SemilocChartRatio.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocChartRatio.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocChartRatio.proof (GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.of_remaining hFibreIncomp)

theorem SemilocRankFrac.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac.proof GroundTheory.Heights₂.Heights.Inter.RankFracDegree.full GroundTheory.Heights₂.Heights.Inter.SemilocFinite.full (GroundTheory.Heights₂.Heights.Inter.SemilocChartRatio.of_remaining hFibreIncomp)

theorem SemilocRankAdjoin.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocRankAdjoin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocRankAdjoin.proof (GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac.of_remaining hFibreIncomp) GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.full

theorem SemilocRank.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocRank.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocRank.proof hFibreDim (GroundTheory.Heights₂.Heights.Inter.SemilocRankAdjoin.of_remaining hFibreIncomp)

theorem FibreDivSupp.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.proof hFibreIncomp

theorem SemilocLengthSum.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocLengthSum.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocLengthSum.proof GroundTheory.Heights₂.Heights.Inter.SemilocFinite.full hSemilocMaxIdeals hSemilocResidueDeg (GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.of_remaining hFibreIncomp) GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.full (GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.of_remaining hFibreIncomp)

theorem SemilocLength.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocLength.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocLength.proof (GroundTheory.Heights₂.Heights.Inter.SemilocLengthSum.of_remaining hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg) (GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.of_remaining hFibreIncomp) GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.full

theorem ArithmeticIntersectionDivisorPushforward.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionDivisorPushforward.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionDivisorPushforward.proof GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.full GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.full GroundTheory.Heights₂.Heights.Inter.SemilocFinite.full (GroundTheory.Heights₂.Heights.Inter.SemilocRank.of_remaining hFibreIncomp hFibreDim) (GroundTheory.Heights₂.Heights.Inter.SemilocLength.of_remaining hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg)

theorem ArithmeticIntersectionCycle.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι')
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.proof GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal.full (GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionVertical.of_remaining hProjDeg) (GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionDivisorPushforward.of_remaining hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg hFibreDim) GroundTheory.Heights₂.Heights.Inter.GenericPointExists.full (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _)

theorem GenericPointsInAffineChart.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement) :
    GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart.proof GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionChartFinite.full hAI3ChartNormCount GroundTheory.Heights₂.Heights.Inter.OrbitCompNonvanish.full

theorem GenericPointsAvoidBadLocus.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement) :
    GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.proof (GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart.of_remaining hAI3ChartNormCount)

theorem GenericPointsCount.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement) :
    GroundTheory.Heights₂.Heights.Inter.GenericPointsCount.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointsCount.proof (GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.of_remaining hAI3ChartNormCount)

theorem PullbackDegreeCount.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount.proof hFibreDim GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.full (GroundTheory.Heights₂.Heights.Inter.GenericPointsCount.of_remaining hAI3ChartNormCount) GroundTheory.Heights₂.Heights.Inter.PullbackVanishingOfNullCycle.full GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.full

theorem IntersectionWithSection.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.IntersectionWithSection.Statement :=
  GroundTheory.Heights₂.Heights.Inter.IntersectionWithSection.proof (ReciprocityTheory.ChartRestriction.G.Geo.resExists_of_hironaka ⟨hGFLogStC, hFinTypeQE⟩) GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.full (GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount.of_remaining hAI3ChartNormCount hFibreDim) GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.full

theorem ArithmeticIntersectionIntegral.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral.proof hPtsIntegrable (GroundTheory.Heights₂.Heights.Inter.IntersectionWithSection.of_remaining hAI3ChartNormCount hFinTypeQE hGFLogStC hFibreDim)

theorem PushforwardArithIntersection.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι')
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement)
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero (GroundTheory.Heights₂.Heights.Inter.RatR.of_remaining hPtsIntegrable) (GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.of_remaining hProjDeg hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg hFibreDim) (GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral.of_remaining hAI3ChartNormCount hFinTypeQE hGFLogStC hFibreDim hPtsIntegrable)

theorem PFSecRed.of_remaining
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.PFSecRed.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PFSecRed.proof (by intros; exact GroundTheory.Heights₂.Heights.Targets.Multilin.full _ _) hFibreDim

theorem PFFibreSum.of_remaining
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.PFFibreSum.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PFFibreSum.proof hFibreDim GroundTheory.Heights₂.Heights.Inter.PFFibreBij.full GroundTheory.Heights₂.Heights.Inter.PFFibreMult.full

theorem PFStep.of_remaining
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.PFStep.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PFStep.proof (GroundTheory.Heights₂.Heights.Inter.PFSecRed.of_remaining hFibreDim) GroundTheory.Heights₂.Heights.Inter.PFVert.full GroundTheory.Heights₂.Heights.Inter.PFIntZero.full GroundTheory.Heights₂.Heights.Inter.PFHoriz.full (GroundTheory.Heights₂.Heights.Inter.PFFibreSum.of_remaining hFibreDim) GroundTheory.Heights₂.Heights.imageArith GroundTheory.Heights₂.Heights.Inter.Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixed

theorem PushforwardProjLineFlag.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι')
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement)
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.PushforwardProjLineFlag.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PushforwardProjLineFlag.proof (GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection.of_remaining hProjDeg hAI3ChartNormCount hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg hFinTypeQE hGFLogStC hFibreDim hPtsIntegrable) (GroundTheory.Heights₂.Heights.Inter.PFStep.of_remaining hFibreDim)

theorem PushforwardProjLineRankTwo.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι')
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement)
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.PushforwardProjLineRankTwo.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PushforwardProjLineRankTwo.proof (GroundTheory.Heights₂.Heights.Inter.PushforwardProjLineFlag.of_remaining hProjDeg hAI3ChartNormCount hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg hFinTypeQE hGFLogStC hFibreDim hPtsIntegrable) hFibreDim (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _) GroundTheory.Heights₂.Heights.Inter.LineFibreBlocks.full

theorem ProjectiveLineOverRationals.of_remaining
    (hTwinPL1 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.PoincareLelongAlt.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ProjectiveLineOverRationals.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ProjectiveLineOverRationals.proof hTwinPL1 GroundTheory.Heights₂.Heights.Inter.BCMult.intersectionNumber_baseChange

theorem RegularityMaximalSpectrum.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSpectrum.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSpectrum.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full GroundTheory.Heights₂.Heights.Inter.RegularityLocalize.full GroundTheory.Heights₂.Heights.Inter.LocRingInj.full hR1RegMaxSurj

theorem RegularityLocal.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityLocal.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocal.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full (GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSpectrum.of_remaining hR1RegMaxSurj)

theorem RegularityFormula.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityFormula.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityFormula.proof GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.full GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full (GroundTheory.Heights₂.Heights.Inter.RegularityLocal.of_remaining hR1RegMaxSurj)

theorem RegularityLocalProduct.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityLocalProduct.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalProduct.proof GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.full (GroundTheory.Heights₂.Heights.Inter.RegularityFormula.of_remaining hR1RegMaxSurj) GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.full GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.full GroundTheory.Heights₂.Heights.Inter.RegularityLocalFinite.full

theorem VerticalEmbedding.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.VerticalEmbedding.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalEmbedding.proof GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.full GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.full (GroundTheory.Heights₂.Heights.Inter.RegularityLocalProduct.of_remaining hR1RegMaxSurj)

theorem VerticalClosedPoints.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.VerticalClosedPoints.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalClosedPoints.proof GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.full (GroundTheory.Heights₂.Heights.Inter.VerticalEmbedding.of_remaining hR1RegMaxSurj)

theorem DiagR.of_remaining
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.DiagR.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DiagR.proof (GroundTheory.Heights₂.Heights.Inter.RatR.of_remaining hPtsIntegrable) GroundTheory.Heights₂.Heights.Inter.DiagDiv.full GroundTheory.Heights₂.Heights.Inter.DiagPullI.full GroundTheory.Heights₂.Heights.Inter.ZeroSetNull.full

theorem PtsAbsMeasurable.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC) :
    GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.proof (ReciprocityTheory.ChartRestriction.G.Geo.resExists_of_hironaka ⟨hGFLogStC, hFinTypeQE⟩)

theorem RPositionAdd.of_remaining
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.RPositionAdd.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RPositionAdd.proof ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite hPtsIntegrable

theorem DeSlotAdd.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC) :
    GroundTheory.Heights₂.Heights.Inter.DeSlotAdd.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DeSlotAdd.proof (ReciprocityTheory.ChartRestriction.G.Geo.resExists_of_hironaka ⟨hGFLogStC, hFinTypeQE⟩)

theorem PoincareLelongAlt.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hDivPushPoint : ReciprocityTheory.ChartRestriction.G.Geo.DivPushPointStatement)
    (hDivPushResSide : ReciprocityTheory.ChartRestriction.G.Geo.DivPushResSideStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula :=
  GroundTheory.Heights₂.Heights.Inter.PoincareLelongAlt.proof ⟨hGFLogStC, hFinTypeQE⟩ hPtsIntegrable hDivPushResSide hDivPushPoint

theorem PtsAddFirst.of_remaining
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.PtsAddFirst.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PtsAddFirst.proof hPtsIntegrable

theorem PtsAbsIntegrable.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.proof hPtsIntegrable (GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.of_remaining hFinTypeQE hGFLogStC)

theorem PtsRegLimit.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.PtsRegLimit.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PtsRegLimit.proof hPtsIntegrable (GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.of_remaining hFinTypeQE hGFLogStC hPtsIntegrable)

theorem PtsMonoSemiPos.of_remaining
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.PtsMonoSemiPos.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PtsMonoSemiPos.proof hPtsIntegrable GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.full

theorem DeLeSemiPos.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hDivPushPoint : ReciprocityTheory.ChartRestriction.G.Geo.DivPushPointStatement)
    (hDivPushResSide : ReciprocityTheory.ChartRestriction.G.Geo.DivPushResSideStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.DeLeSemiPos.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DeLeSemiPos.proof (GroundTheory.Heights₂.Heights.Inter.PoincareLelongAlt.of_remaining hFinTypeQE hGFLogStC hDivPushPoint hDivPushResSide hPtsIntegrable) (ReciprocityTheory.ChartRestriction.G.Geo.stokes_of_hironaka ⟨hGFLogStC, hFinTypeQE⟩) (GroundTheory.Heights₂.Heights.Inter.PtsAddFirst.of_remaining hPtsIntegrable) (GroundTheory.Heights₂.Heights.Inter.PtsRegLimit.of_remaining hFinTypeQE hGFLogStC hPtsIntegrable) (GroundTheory.Heights₂.Heights.Inter.PtsMonoSemiPos.of_remaining hPtsIntegrable) GroundTheory.Heights₂.Heights.Inter.RegCurvBound.full GroundTheory.Heights₂.Heights.Inter.HorizNotMem.full

theorem ProjectiveLineTwo.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hDivPushPoint : ReciprocityTheory.ChartRestriction.G.Geo.DivPushPointStatement)
    (hDivPushResSide : ReciprocityTheory.ChartRestriction.G.Geo.DivPushResSideStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    ReciprocityTheory.ChartRestriction.G.Geo.SectionSpaceSymmetry :=
  GroundTheory.Heights₂.Heights.Inter.ProjectiveLineTwo.proof (GroundTheory.Heights₂.Heights.Inter.DeSlotAdd.of_remaining hFinTypeQE hGFLogStC) GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.full (GroundTheory.Heights₂.Heights.Inter.DeLeSemiPos.of_remaining hFinTypeQE hGFLogStC hDivPushPoint hDivPushResSide hPtsIntegrable)

theorem Swap.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hDivPushPoint : ReciprocityTheory.ChartRestriction.G.Geo.DivPushPointStatement)
    (hDivPushResSide : ReciprocityTheory.ChartRestriction.G.Geo.DivPushResSideStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.Swap.Statement :=
  GroundTheory.Heights₂.Heights.Inter.Swap.proof GroundTheory.Heights₂.Heights.Inter.SwapCycles.full GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.GeoNumCut (GroundTheory.Heights₂.Heights.Inter.ProjectiveLineTwo.of_remaining hFinTypeQE hGFLogStC hDivPushPoint hDivPushResSide hPtsIntegrable)

theorem ThmISymm.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreComp : ReciprocityTheory.ChartRestriction.G.AI.I2.FibreCompStatement)
    (hDivPushPoint : ReciprocityTheory.ChartRestriction.G.Geo.DivPushPointStatement)
    (hDivPushResSide : ReciprocityTheory.ChartRestriction.G.Geo.DivPushResSideStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.ThmISymm.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ThmISymm.proof (GroundTheory.Heights₂.Heights.Inter.Swap.of_remaining hFinTypeQE hGFLogStC hDivPushPoint hDivPushResSide hPtsIntegrable) (GroundTheory.Heights₂.Heights.Inter.RPositionAdd.of_remaining hPtsIntegrable) hFibreComp (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.SymmStatement.full _ _) (by intros; exact GroundTheory.Heights₂.Heights.geoNumStatement _)

theorem ProjectivePlaneOverRationals.of_remaining
    (hTwinPL2 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ProjectiveLineTwo.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ProjectivePlaneOverRationals.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ProjectivePlaneOverRationals.proof hTwinPL2 GroundTheory.Heights₂.Heights.Inter.BCMult.intersectionNumber_baseChange

theorem IndefiniteRowSideFullHecke.ResExists.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResExists.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResExists.proof ⟨hGFLogStC, hFinTypeQE⟩

theorem IndefiniteRowSideFullHecke.Degrees.of_remaining
    (hTwinPL1 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.PoincareLelongAlt.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.proof hTwinPL1 (GroundTheory.Heights₂.Heights.Inter.IndefiniteRowSideFullHecke.ResExists.of_remaining hFinTypeQE hGFLogStC) GroundTheory.Heights₂.Heights.Inter.Closed.IndefiniteRowSideFullHecke.ZIntPoint

theorem WellDefined.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hDivPushPoint : ReciprocityTheory.ChartRestriction.G.Geo.DivPushPointStatement)
    (hDivPushResSide : ReciprocityTheory.ChartRestriction.G.Geo.DivPushResSideStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.WellDefined.Statement :=
  GroundTheory.Heights₂.Heights.Inter.WellDefined.proof (GroundTheory.Heights₂.Heights.Inter.Swap.of_remaining hFinTypeQE hGFLogStC hDivPushPoint hDivPushResSide hPtsIntegrable) (GroundTheory.Heights₂.Heights.Inter.RPositionAdd.of_remaining hPtsIntegrable)

theorem RegularityProductFormula.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityProductFormula.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityProductFormula.proof GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.full (GroundTheory.Heights₂.Heights.Inter.VerticalClosedPoints.of_remaining hR1RegMaxSurj)

theorem RegularityIndependence.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite (GroundTheory.Heights₂.Heights.Inter.RegularityProductFormula.of_remaining hR1RegMaxSurj)

theorem RMul.of_remaining
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.RMulStatement :=
  GroundTheory.Heights₂.Heights.Inter.RMul.proof hPtsIntegrable

theorem ThmIExists.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreComp : ReciprocityTheory.ChartRestriction.G.AI.I2.FibreCompStatement)
    (hDivPushPoint : ReciprocityTheory.ChartRestriction.G.Geo.DivPushPointStatement)
    (hDivPushResSide : ReciprocityTheory.ChartRestriction.G.Geo.DivPushResSideStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.ThmIExists.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ThmIExists.proof (GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.of_remaining hR1RegMaxSurj) (GroundTheory.Heights₂.Heights.Inter.RMul.of_remaining hPtsIntegrable) (GroundTheory.Heights₂.Heights.Inter.WellDefined.of_remaining hFinTypeQE hGFLogStC hDivPushPoint hDivPushResSide hPtsIntegrable) (GroundTheory.Heights₂.Heights.Inter.ThmISymm.of_remaining hFinTypeQE hGFLogStC hFibreComp hDivPushPoint hDivPushResSide hPtsIntegrable)

theorem R1.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.R1.Statement :=
  GroundTheory.Heights₂.Heights.Inter.R1.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite (GroundTheory.Heights₂.Heights.Inter.RegularityProductFormula.of_remaining hR1RegMaxSurj)

theorem PropAPrime.of_remaining
    (hFibreInt : GroundTheory.Heights₂.Heights.Inter.FibreInt.Statement)
    (hToFibreSquare : GroundTheory.Heights₂.Heights.Inter.ToFibreSquare.Statement) :
    GroundTheory.Heights₂.Heights.Inter.PropAPrime.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PropAPrime.proof hToFibreSquare hFibreInt

theorem TheoremA.of_remaining
    (hFibreInt : GroundTheory.Heights₂.Heights.Inter.FibreInt.Statement)
    (hSettingP0 : GroundTheory.Heights₂.Heights.Inter.ProjectivePointSetting.Statement)
    (hToFibreSquare : GroundTheory.Heights₂.Heights.Inter.ToFibreSquare.Statement) :
    GroundTheory.Heights₂.Heights.Inter.TheoremA.Statement :=
  GroundTheory.Heights₂.Heights.Inter.TheoremA.proof hSettingP0 (GroundTheory.Heights₂.Heights.Inter.PropAPrime.of_remaining hFibreInt hToFibreSquare)

theorem ThmIMultilin.of_remaining
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreComp : ReciprocityTheory.ChartRestriction.G.AI.I2.FibreCompStatement)
    (hDivPushPoint : ReciprocityTheory.ChartRestriction.G.Geo.DivPushPointStatement)
    (hDivPushResSide : ReciprocityTheory.ChartRestriction.G.Geo.DivPushResSideStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.proof (GroundTheory.Heights₂.Heights.Inter.ThmISymm.of_remaining hFinTypeQE hGFLogStC hFibreComp hDivPushPoint hDivPushResSide hPtsIntegrable)

theorem DegreesQ.of_remaining
    (hTwinPL1 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.PoincareLelongAlt.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.DegreesQ.Statement :=
  GroundTheory.Heights₂.Heights.Inter.DegreesQ.proof (GroundTheory.Heights₂.Heights.Inter.IndefiniteRowSideFullHecke.Degrees.of_remaining hTwinPL1 hFinTypeQE hGFLogStC)

theorem BaseChange.of_remaining
    (hTwinPL1 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.PoincareLelongAlt.Statement)
    (hTwinPL2 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ProjectiveLineTwo.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ProjectiveLineOverRationals.Statement ∧ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ProjectivePlaneOverRationals.Statement ∧ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.DegreesQ.Statement :=
  GroundTheory.Heights₂.Heights.Inter.BaseChange.proof hTwinPL1 hTwinPL2 (GroundTheory.Heights₂.Heights.Inter.IndefiniteRowSideFullHecke.Degrees.of_remaining hTwinPL1 hFinTypeQE hGFLogStC) GroundTheory.Heights₂.Heights.Inter.BCMult.intersectionNumber_baseChange

theorem PFCoord.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι')
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement)
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement :=
  GroundTheory.Heights₂.Heights.Targets.PFCoord.of_found (GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection.of_remaining hProjDeg hAI3ChartNormCount hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg hFinTypeQE hGFLogStC hFibreDim hPtsIntegrable) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _) GroundTheory.Heights₂.Heights.Targets.genFibreExists hFibreDim GroundTheory.Heights₂.Heights.Inter.Closed.Targets.CoordFibreDeg

theorem ArithIntersectionSystem.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι')
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement)
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreComp : ReciprocityTheory.ChartRestriction.G.AI.I2.FibreCompStatement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement)
    (hDivPushPoint : ReciprocityTheory.ChartRestriction.G.Geo.DivPushPointStatement)
    (hDivPushResSide : ReciprocityTheory.ChartRestriction.G.Geo.DivPushResSideStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement :=
  GroundTheory.Heights₂.Heights.Targets.ArithIntersectionSystem.of_found (GroundTheory.Heights₂.Heights.Inter.ThmIExists.of_remaining hR1RegMaxSurj hFinTypeQE hGFLogStC hFibreComp hDivPushPoint hDivPushResSide hPtsIntegrable) (GroundTheory.Heights₂.Heights.Inter.PFCoord.of_remaining hProjDeg hAI3ChartNormCount hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg hFinTypeQE hGFLogStC hFibreDim hPtsIntegrable) GroundTheory.Heights₂.Heights.Inter.Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixed

theorem PFSum.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι')
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement)
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFSumStatement :=
  GroundTheory.Heights₂.Heights.Targets.PFSum.of_found (GroundTheory.Heights₂.Heights.Inter.RatR.of_remaining hPtsIntegrable) (GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.of_remaining hProjDeg hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg hFibreDim) (GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral.of_remaining hAI3ChartNormCount hFinTypeQE hGFLogStC hFibreDim hPtsIntegrable)

theorem TheoremI.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement)
    (hFinTypeQE : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hGFLogStC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC)
    (hFibreComp : ReciprocityTheory.ChartRestriction.G.AI.I2.FibreCompStatement)
    (hDivPushPoint : ReciprocityTheory.ChartRestriction.G.Geo.DivPushPointStatement)
    (hDivPushResSide : ReciprocityTheory.ChartRestriction.G.Geo.DivPushResSideStatement)
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.TheoremIStatement :=
  And.intro (GroundTheory.Heights₂.Heights.Inter.ThmIExists.of_remaining hR1RegMaxSurj hFinTypeQE hGFLogStC hFibreComp hDivPushPoint hDivPushResSide hPtsIntegrable) (And.intro GroundTheory.Heights₂.Heights.Inter.Closed.ReciprocityTheory.ChartRestriction.G.AI.I2.Unique (And.intro (GroundTheory.Heights₂.Heights.Inter.ThmISymm.of_remaining hFinTypeQE hGFLogStC hFibreComp hDivPushPoint hDivPushResSide hPtsIntegrable) (GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.of_remaining hFinTypeQE hGFLogStC hFibreComp hDivPushPoint hDivPushResSide hPtsIntegrable)))

end GroundTheory.Heights₂.Heights.Inter
