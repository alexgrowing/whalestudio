import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PAddHeightsridge
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PChartLatNmSection
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PChartLatSection
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PDualBasisExists
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.WeightedHomogeneousComponentMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Imports
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsArithVarOfRingKrullDim
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZero
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PFibreCompDimZ
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DetGramLeProdNormSq
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.VolumeFundamentalDomainEq
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroAlt
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroBis
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PHomogGeneratorsExist
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIdealIndexPlaces
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLatticeLineExists
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLineDegreeBundle
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLineIdealDual
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockPoints
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockStandard
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PPointHeightDegree
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PReadsMul
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PSectionSmall
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartPowNeZero
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartMonomialMemOfNotIsLive
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MemPointsOfGeneratorsVanish
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsAlgebraicNew
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsFormOfMemChartRing
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.NormSqEvalConeScale
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExtMapLiftOldOfIsWeightedHomogeneous
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExtVal
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.WeightEqMapDomain
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AnalyticAtEvalConeComp
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LiftOldChartMonomialMemPrimeCompl
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomial
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsWeightedHomogeneousAeval
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroTer
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.BirationalOfBlock
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsWeightedHomogeneousSepBlock
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.VarsSubsetRangeBlockIncl
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroMore
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.CardLeOfSeparated
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MonomialValuesOneBlock
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusMetric
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusSec
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusSmall
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusSupSmall
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartFormEvalAgree
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LinearIndependentOfMemSpan
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.HilbDegreeBoundAltOfStatement
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsWeightedHomogeneousMonomialOf
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsOneBlockLinMonomial
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsNatMulIsIntegralFin
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LatticePointPairForms
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartRingDescriptionAltHolds
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MapCompExtMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeConj
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsExtra
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsRest
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsSide
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FiniteTwistsDegreeFormOfFirst
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MemChartRingZOfMemChartRing
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsTail
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MemConePointsProjIdealIff
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.RenameBlockIsWeightedHomogeneous
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LocalChangeOfVectorSpace
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IntDomainDim.full : IntDomainDim.Statement :=
  IntDomainDim.proof

theorem ConeTrdeg.full : ConeTrdeg.Statement :=
  ConeTrdeg.proof

theorem FibreCompDimZ.full : FibreCompDimZ.Statement :=
  FibreCompDimZ.proof

theorem WeightedDegree.full : WeightedDegree.Statement :=
  WeightedDegree.proof

theorem ChartFormsAlt.full : ChartFormsAlt.Statement :=
  ChartFormsAlt.proof

theorem ChartCrossRatio.full : ChartCrossRatio.Statement :=
  ChartCrossRatio.proof

theorem ChartVanishing.full : ChartVanishing.Statement :=
  ChartVanishing.proof

theorem ChartPrimality.full : ChartPrimality.Statement :=
  ChartPrimality.proof

theorem ExtensionDimension.full : ExtensionDimension.Statement :=
  ExtensionDimension.proof

theorem ChartRingDescription.full : ChartRingDescription.Statement :=
  ChartRingDescription.proof

theorem HomogGeneratorsExist.full : HomogGeneratorsExist.Statement :=
  HomogGeneratorsExist.proof

theorem SectionCycle.full : SectionCycle.Statement :=
  SectionCycle.proof

theorem BlockSurjectivity.full : BlockSurjectivity.Statement :=
  BlockSurjectivity.proof

theorem SectionInjectivity.full : SectionInjectivity.Statement :=
  SectionInjectivity.proof

theorem LatticePacking.full : LatticePacking.Statement :=
  LatticePacking.proof

theorem HadamardGramBound.full : HadamardGramBound.Statement :=
  HadamardGramBound.proof

theorem MonomialMap.full : MonomialMap.Statement :=
  MonomialMap.proof

theorem MonomialMapNorm.full : MonomialMapNorm.Statement :=
  MonomialMapNorm.proof

theorem SpanningAtDominantWeight.full : SpanningAtDominantWeight.Statement :=
  SpanningAtDominantWeight.proof

theorem LatticePointCount.full : LatticePointCount.Statement :=
  LatticePointCount.proof

theorem BoundedMonomials.full : BoundedMonomials.Statement :=
  BoundedMonomials.proof

theorem SectionSmall.full : SectionSmall.Statement :=
  SectionSmall.proof

theorem DualBasisExists.full : DualBasisExists.Statement :=
  DualBasisExists.proof

theorem OneBlockStandard.full : OneBlockStandard.Statement :=
  OneBlockStandard.proof

theorem OneBlockPoints.full : OneBlockPoints.Statement :=
  OneBlockPoints.proof

theorem ChartLatSection.full : ChartLatSection.Statement :=
  ChartLatSection.proof

theorem ChartLatNmSection.full : ChartLatNmSection.Statement :=
  ChartLatNmSection.proof

theorem ReadsMul.full : ReadsMul.Statement :=
  ReadsMul.proof

theorem YPlusSec.full : YPlusSec.Statement :=
  YPlusSec.proof

theorem LineIdealDual.full : LineIdealDual.Statement :=
  LineIdealDual.proof

theorem IdealIndexPlaces.full : IdealIndexPlaces.Statement :=
  IdealIndexPlaces.proof

theorem ConePoints.full : ConePoints.Statement :=
  ConePoints.proof ChartVanishing.full

theorem ConePointsConverse.full : ConePointsConverse.Statement :=
  ConePointsConverse.proof ChartVanishing.full

theorem ChartDenominatorAlt.full : ChartDenominatorAlt.Statement :=
  ChartDenominatorAlt.proof ChartVanishing.full

theorem ChartMetric.full : ChartMetric.Statement :=
  ChartMetric.proof ChartDenominatorAlt.full ConePoints.full ChartCrossRatio.full

theorem PlurisubharmonicMetric.full : PlurisubharmonicMetric.Statement :=
  PlurisubharmonicMetric.proof ConePoints.full ChartMetric.full

theorem SectionNorm.full : SectionNorm.Statement :=
  SectionNorm.proof ConePoints.full ChartMetric.full

theorem SmallSections.full : SmallSections.Statement :=
  SmallSections.proof ChartFormsAlt.full

theorem SupNormEquality.full : SupNormEquality.Statement :=
  SupNormEquality.proof BlockSurjectivity.full

theorem BlockImage.full : BlockImage.Statement :=
  BlockImage.proof IntDomainDim.full ConeTrdeg.full

theorem GeometricArithmeticNumbers.full : GeometricArithmeticNumbers.Statement :=
  GeometricArithmeticNumbers.proof WeightedDegree.full FibreCompDimZ.full

theorem FibrePoints.full : FibrePoints.Statement :=
  FibrePoints.proof GeometricArithmeticNumbers.full

theorem LatticeLineExists.full : LatticeLineExists.Statement :=
  LatticeLineExists.proof OneBlockPoints.full

theorem PointHeightDegree.full : PointHeightDegree.Statement :=
  PointHeightDegree.proof OneBlockPoints.full LatticeLineExists.full LineIdealDual.full IdealIndexPlaces.full

theorem AddBlockBridge.full : AddBlockBridge.Statement :=
  AddBlockBridge.proof ChartLatSection.full

theorem YPlusArithVar.full : YPlusArithVar.Statement :=
  YPlusArithVar.proof ChartPrimality.full ExtensionDimension.full

theorem YPlusMetric.full : YPlusMetric.Statement :=
  YPlusMetric.proof ChartFormsAlt.full HomogGeneratorsExist.full ChartMetric.full ConePoints.full

theorem YPlusSmall.full : YPlusSmall.Statement :=
  YPlusSmall.proof ChartFormsAlt.full ConePointsConverse.full

theorem YPlusSupSmall.full : YPlusSupSmall.Statement :=
  YPlusSupSmall.proof ChartFormsAlt.full ConePoints.full

theorem OneBlockModel.full : OneBlockModel.Statement :=
  OneBlockModel.proof (CoordConeArithVar.proof IntDomainDim.full)

end GroundTheory.Heights₂.Heights

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem WeightedDegree.full : WeightedDegree.Statement :=
  WeightedDegree.equiv.mp GroundTheory.Heights₂.Heights.WeightedDegree.full

theorem BoundedMonomials.full : BoundedMonomials.Statement :=
  BoundedMonomials.equiv.mp GroundTheory.Heights₂.Heights.BoundedMonomials.full

theorem HadamardGramBound.full : HadamardGramBound.Statement :=
  HadamardGramBound.equiv.mp GroundTheory.Heights₂.Heights.HadamardGramBound.full

theorem MonomialMap.full : MonomialMap.Statement :=
  MonomialMap.equiv.mp GroundTheory.Heights₂.Heights.MonomialMap.full

theorem OneBlockPoints.full : OneBlockPoints.Statement :=
  OneBlockPoints.equiv.mp GroundTheory.Heights₂.Heights.OneBlockPoints.full

theorem ChartRingDescription.full : ChartRingDescription.Statement :=
  ChartRingDescription.equiv.mp GroundTheory.Heights₂.Heights.ChartRingDescription.full

theorem ChartCrossRatio.full : ChartCrossRatio.Statement :=
  ChartCrossRatio.equiv.mp GroundTheory.Heights₂.Heights.ChartCrossRatio.full

theorem ChartDenominatorAlt.full : ChartDenominatorAlt.Statement :=
  ChartDenominatorAlt.equiv.mp GroundTheory.Heights₂.Heights.ChartDenominatorAlt.full

theorem ExtensionDimension.full : ExtensionDimension.Statement :=
  ExtensionDimension.equiv.mp GroundTheory.Heights₂.Heights.ExtensionDimension.full

theorem ChartFormsAlt.full : ChartFormsAlt.Statement :=
  ChartFormsAlt.equiv.mp GroundTheory.Heights₂.Heights.ChartFormsAlt.full

theorem ChartMetric.full : ChartMetric.Statement :=
  ChartMetric.equiv.mp GroundTheory.Heights₂.Heights.ChartMetric.full

theorem ConePointsConverse.full : ConePointsConverse.Statement :=
  ConePointsConverse.equiv.mp GroundTheory.Heights₂.Heights.ConePointsConverse.full

theorem ConePoints.full : ConePoints.Statement :=
  ConePoints.equiv.mp GroundTheory.Heights₂.Heights.ConePoints.full

theorem ChartPrimality.full : ChartPrimality.Statement :=
  ChartPrimality.equiv.mp GroundTheory.Heights₂.Heights.ChartPrimality.full

theorem SectionCycle.full : SectionCycle.Statement :=
  SectionCycle.equiv.mp GroundTheory.Heights₂.Heights.SectionCycle.full

theorem SmallSections.full : SmallSections.Statement :=
  SmallSections.equiv.mp GroundTheory.Heights₂.Heights.SmallSections.full

theorem ChartVanishing.full : ChartVanishing.Statement :=
  ChartVanishing.equiv.mp GroundTheory.Heights₂.Heights.ChartVanishing.full

theorem BlockSurjectivity.full : BlockSurjectivity.Statement :=
  BlockSurjectivity.equiv.mp GroundTheory.Heights₂.Heights.BlockSurjectivity.full

theorem SupNormEquality.full : SupNormEquality.Statement :=
  SupNormEquality.equiv.mp GroundTheory.Heights₂.Heights.SupNormEquality.full

theorem SectionInjectivity.full : SectionInjectivity.Statement :=
  SectionInjectivity.equiv.mp GroundTheory.Heights₂.Heights.SectionInjectivity.full

theorem LatticePacking.full : LatticePacking.Statement :=
  LatticePacking.equiv.mp GroundTheory.Heights₂.Heights.LatticePacking.full

theorem SectionNorm.full : SectionNorm.Statement :=
  (SectionNorm.equiv GroundTheory.Heights₂.Heights.ChartMetric.full).mp GroundTheory.Heights₂.Heights.SectionNorm.full

theorem LatticePointCount.full : LatticePointCount.Statement :=
  LatticePointCount.hilbDegreeBound_alt_of_statement GroundTheory.Heights₂.Heights.LatticePointCount.full

theorem OneBlockModel.full : OneBlockModel.Statement :=
  OneBlockModel.imp GroundTheory.Heights₂.Heights.OneBlockModel.full

theorem LineDegreeBundle.full : LineDegreeBundle.Statement :=
  LineDegreeBundle.proof

theorem PointHeightDegree.full : PointHeightDegree.Statement :=
  PointHeightDegree.forward LineDegreeBundle.full GroundTheory.Heights₂.Heights.PointHeightDegree.full

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
