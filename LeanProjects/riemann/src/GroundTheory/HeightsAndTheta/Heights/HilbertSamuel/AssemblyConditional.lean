import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Assembly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAmpleOfGenTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockComplexGramMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockDefectMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageDatum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockRealGramComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLatticeNested
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClopenComponents
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClopenDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexGramMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDefectMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreSectionLift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFrameChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.EventuallyBlocksNeZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ZcombIsConjInvariantH
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenKoszulStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistVanish
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertSamuelProjective
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftAtPrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftPrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricToFS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefSectionGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefShiftPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRational
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPieceIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionToProjective
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionToProjectiveBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecondVeronese
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSlopeLowerBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTheoremHSM
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTheoremHSMBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopPullFS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockChainSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockPieceCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockStepLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseChi
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseTop
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBaseChange
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDegrees
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsArithVarNoBlocks
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem TheoremHSM.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGramMono.Statement)
    (h11 : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel.Statement)
    (h12 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphDeg.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSM.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSM.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SecondVeronese.proof VeroneseArith.full VeroneseSemipos.full
  VeroneseResolution.full (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseChi.proof VeroneseMonoBasis.full h10)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseTop.proof h11 VeroneseArith.full VeroneseGraphImage.full h12)
  VeroneseGenDeg.full) PointHeightFS.full) ResolutionSupBound.full)

theorem TheoremHSMBlock.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionImageSup.Statement)
    (h11 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionDegreeIntegral.Statement)
    (h12 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.Statement)
    (h13 : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (h14 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.Statement)
    (h15 : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel.Statement)
    (h16 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphDeg.Statement)
    (h17 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGramMono.Statement)
    (h18 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphDeg.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSMBlock.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSMBlock.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjectiveBlock.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockMetricChange.proof BlockMeasureChange.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockDefectMetricChange.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockRealGramComparison.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionSupBound.proof h10 NonvanishingDense.full) SupBoundBlock.full
  SupBoundCount.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockComplexGramMetricChange.proof MetricChange.full
  BlockResolutionMetricPair.full BlockResolutionFormsIndependent.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionDegree.proof BlockSectionsRank.full h11))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedIntegral.proof h12 BlockResolutionInterpIntegral.full)
  (GroundTheory.Heights₂.Heights.PtsIntegrable.of_found h13 Closed.PtsSumMeasurable)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageDatum.proof BlockImageArith.full h14 AnResNullForm.full
  BlockImageMetrics.full BlockImageChi.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageTop.proof h15
  BlockGraphImage.full h16) BlockImageGenDeg.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SecondVeronese.proof VeroneseArith.full VeroneseSemipos.full
  VeroneseResolution.full (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseChi.proof VeroneseMonoBasis.full h17)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseTop.proof h15 VeroneseArith.full VeroneseGraphImage.full h18)
  VeroneseGenDeg.full) PointHeightFS.full) SupBoundBlock.full)

theorem HilbertSamuelProjective.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGramMono.Statement)
    (h11 : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel.Statement)
    (h12 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphDeg.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SecondVeronese.proof VeroneseArith.full VeroneseSemipos.full
  VeroneseResolution.full (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseChi.proof VeroneseMonoBasis.full h10)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseTop.proof h11 VeroneseArith.full VeroneseGraphImage.full h12)
  VeroneseGenDeg.full) PointHeightFS.full)

theorem ReductionToProjective.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))

theorem SlopeLowerBound.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGramMono.Statement)
    (h11 : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel.Statement)
    (h12 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphDeg.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.SlopeLowerBound.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SlopeLowerBound.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSM.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SecondVeronese.proof VeroneseArith.full VeroneseSemipos.full
  VeroneseResolution.full (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseChi.proof VeroneseMonoBasis.full h10)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseTop.proof h11 VeroneseArith.full VeroneseGraphImage.full h12)
  VeroneseGenDeg.full) PointHeightFS.full) ResolutionSupBound.full) RankOfSections.full GenericFibre.full
  SectionsRank.full DegreePositive.full)

theorem SuccessiveMinimaDual.of_open
    (h0 : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.IrreducibleConnected.Statement)
    (h2 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.PoincareLelongAlt.Statement)
    (h3 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResExists.Statement)
    (h4 : GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResInt.Statement)
    (h5 : GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentsAdditive.Statement)
    (h6 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.IntBridge.Statement)
    (h7 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResComps.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.SuccessiveMinimaDual.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SuccessiveMinimaDual.proof G1.full EmbeddingWeight.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersection.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof
  (GroundTheory.Heights₂.Heights.PtsIntegrable.of_found h0 Closed.PtsSumMeasurable))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegree.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.PieceIntegral.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ClopenDegree.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.ClopenComponents.proof
  h1) (GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentDegree.proof (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.proof h2 h3
  Closed.IndefiniteRowSideFullHecke.Inter.ZIntPoint) h3 h4) h5 IntNumComponents.full)) ConjIntNum.full))
  (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.DegreeGeneric.of_degreesQ h6 h7 (GroundTheory.Heights₂.Heights.Inter.DegreesQ.proof
  (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.proof h2 h3 Closed.IndefiniteRowSideFullHecke.Inter.ZIntPoint)))))

theorem G2.of_open
    (h0 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.IntBridge.Statement)
    (h1 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResComps.Statement)
    (h2 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.PoincareLelongAlt.Statement)
    (h3 : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ResExists.Statement)
    (h4 : GroundTheory.Heights₂.Heights.HilbertSamuel.FujitaGeneric.Statement)
    (h5 : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartLatQCech.Statement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.EulerHilbert.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionLatticeFinite.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.DiagonalSectionDifference.Statement)
    (h9 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KAmpStatement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleFibre.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.G2.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.G2.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaSection.proof
  NefOnGenericOfSemipos.full (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.DegreeGeneric.of_degreesQ h0 h1
  (GroundTheory.Heights₂.Heights.Inter.DegreesQ.proof (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.proof h2 h3
  Closed.IndefiniteRowSideFullHecke.Inter.ZIntPoint))) (GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.NefSectionGrowth.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.NefShiftPolynomial.proof h4 h5 h6 EventualPolyLine.full)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftSectionBound.proof h7
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftQuotientBound.proof h7
  (GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneQuotientBound.proof HyperplaneRegularSection.full h8 h7)
  HyperplaneRegularSection.full))) (GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneSectionBound.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneQuotientBound.proof HyperplaneRegularSection.full h8 h7)))
  ChartDenominator.full SectionSupBound.full) SectionProduct.full PerturbSemipos.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleGeneric.proof h9
  (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.DegreeGeneric.of_degreesQ h0 h1 (GroundTheory.Heights₂.Heights.Inter.DegreesQ.proof
  (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Degrees.proof h2 h3 Closed.IndefiniteRowSideFullHecke.Inter.ZIntPoint)))) h10 ZCombLimit.full)

theorem Lift.of_open
    (h0 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KAmpStatement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleFibre.Statement)
    (h2 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement)
    (h3 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDSqStatement)
    (h4 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDDegStatement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.Lift.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.Lift.proof h0 h1 (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftModel.proof
  LiftSpread.full (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftAtPrime.proof GeneratedPow.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.FibreSectionLift.proof h2 QuotPartGraded.full h3 h4 ReductionComplex.full
  ZeroCocycleSection.full SecCochReduce.full) FibreRelLift.full) LiftBirationalAmple.full))

theorem LiftPrime.of_open
    (h0 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KAmpStatement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleFibre.Statement)
    (h2 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement)
    (h3 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDSqStatement)
    (h4 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDDegStatement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.LiftPrime.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftPrime.proof (GroundTheory.Heights₂.Heights.HilbertSamuel.Lift.proof h0 h1
  (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftModel.proof LiftSpread.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftAtPrime.proof GeneratedPow.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.FibreSectionLift.proof h2 QuotPartGraded.full h3 h4 ReductionComplex.full
  ZeroCocycleSection.full SecCochReduce.full) FibreRelLift.full) LiftBirationalAmple.full)))

theorem Perturb.of_open
    (h0 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.KoszulCechComplex.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.KoszulCechExact.Statement)
    (h3 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDSqStatement)
    (h4 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechDDegStatement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.Perturb.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.Perturb.proof SmallGenTwist.full SemiposTwist.full GenDegTwist.full
  GenOnFibres.full (GroundTheory.Heights₂.Heights.HilbertSamuel.AmpleOfGenTwist.proof GenTwistGenerated.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistVanish.proof h0 QuotPartGraded.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.GenKoszulStep.proof h1 h2 DoubleComplexVanish.full h3 h4))))

theorem IntegralClosureFinite.of_open
    (h0 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.SecEqStatement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralClosureFinite.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralClosureFinite.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsRational.proof h0) NmSectionsFinite.full)

end GroundTheory.Heights₂.Heights.HilbertSamuel
