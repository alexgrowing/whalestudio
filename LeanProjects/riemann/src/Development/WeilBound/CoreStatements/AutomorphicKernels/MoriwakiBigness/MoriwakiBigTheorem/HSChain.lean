import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiBig
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.KeyFormulaVanishingCechMultInvariants
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNef
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAddBlockIsometric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAmpleOfGenTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PArithKleiman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockChiCovolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGen
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtChartUnit
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtFibreLift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtGenUniform
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtSkyscraper
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexMinimalPrimesContract
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurveSmallCountLower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDoubleComplexVanish
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSections
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSectionsPower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFSGeomDegPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRelLift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreSectionLift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ZcombIsConjInvariantH
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelConstShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Imports
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CharZeroOfIsHorizontal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CoeffLeOfEvalLeMul
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LeLimsupDiv
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.UnipotentCharacter
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConjInvariantHZcomb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegGeomDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenKoszulStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenNearCover
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenNearMul
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistVanish
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedNefGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedPow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubmodules
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.H1VanishGeneratedOfLocalizedSubsingleton
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIndependentModBaseChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIsomInvariance
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanNefF
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanScheme
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.VanishOfVanishNsmul
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKoszulCechComplex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKoszulCechExact
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviCompHol
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviFSInvariant
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviHolPerturb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviLogFlat
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftAtPrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocIdealKer
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleiman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleimanLow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleimanTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedSectionStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMonomialShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefPlusAmpleDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerHeightsirational
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockDatum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockMeasure
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockMetric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockOldPartSurj
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockPointNorm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockVeronese
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeComplexRadical
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeZariskiDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionComplex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResVolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSHProps
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSTopPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecCochReduce
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsMultiHomogSumSmulMap
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionNormSqExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionRingFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSeparatedSmallCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftNefBig
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftSectionSeparation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionMixed
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUpperNormalisation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZeroCocycleSection
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldLeLocRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDDeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDSq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechMapDeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechSES
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCombContract
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCombCyclic
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeBadFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeDecomp
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeEmbed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeIndep
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHPrimeFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremS
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremSFree
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAmpleCountAlongMultiplesX
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNefBigCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNumberFieldBoxCountX
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSFull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PAmpleCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartLatFull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveBoxCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveBoxLattice
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveBoxSmall
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveClosedPointChart
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveCountLower
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveDegreeVert
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveEmbedOrbit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveFieldNumber
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveIndexLinear
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveRingFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotLocal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertIndex
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointChart
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointInj
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointLength
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointMultChart
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointNagata
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointResidue
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointSurj
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PInvertibleIndexCharP
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PInvertibleIndexMul
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PInvertibleProductRep
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftBlockDatum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphPoints
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLocalGenFamily
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLocallyPrincipalCoprimeField
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PMoriwakiBigCurve
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInputStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanInputNefAmpleSectionCountStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KodairaGenericOfAmpleSectionCountStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormFormGaussBoundHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolutionStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.SegreJoinGeneration.GeneratesOverSegreJoinTwist
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelBlock.HSMBlock
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiRankBounds.OfAis

noncomputable section

namespace PositivityTheory.Pf1.HilbertSamuelMoriwaki

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter MvPolynomial

theorem hsChain (hResK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) (hAIS : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement)
    (hDBH : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.DenseBoundedHeight.Statement) :
    GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeBig.Statement ∧ GroundTheory.Heights₂.Heights.Targets.MoriwakiBigCurve.Statement ∧
      GroundTheory.Heights₂.Heights.HilbertSamuel.ArithKleiman.Statement ∧ GroundTheory.Heights₂.Heights.HilbertSamuel.G7.Statement ∧
      GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeNef.Statement := by
  have s1 := GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.proof
  have s2 := GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDenominator.proof
  have s3 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSupBound.proof
  have s4 := GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaSection.proof s1 (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS)) (GlobalTheory.T.kodaira_generic_of_ample_section_count (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.1 (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.2) s2 s3
  have s5 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionProduct.full
  have s6 := GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbSemipos.proof
  have s7 := GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleGeneric.proof (PositivityTheory.KAmp.kAmp) (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS))
  have s8 := GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt.full
  have s9 := GroundTheory.Heights₂.Heights.Kleiman.KHCechDSq.full
  have s10 := GroundTheory.Heights₂.Heights.Kleiman.KHCechDDeg.full
  have s11 := GroundTheory.Heights₂.Heights.Kleiman.KHCechSES.proof s9 s10
  have s12 := GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot.full
  have s13 := GroundTheory.Heights₂.Heights.HilbertSamuel.H1VanishingDevissage.proof s8 s11 s12
  have s14 := GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubmodules.proof
  have s15 := GroundTheory.Heights₂.Heights.HilbertSamuel.ClosedPtChartUnit.proof
  have s16 := GroundTheory.Heights₂.Heights.HilbertSamuel.ClosedPtSkyscraper.proof s15
  have s17 := GroundTheory.Heights₂.Heights.HilbertSamuel.LocIdealKer.proof
  have s18 := GroundTheory.Heights₂.Heights.HilbertSamuel.ClosedPtFibreLift.proof s14 s11 s16 s17
  have s19 := GroundTheory.Heights₂.Heights.HilbertSamuel.ChartNakayamaGen.proof
  have s20 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenNearMul.proof
  have s21 := GroundTheory.Heights₂.Heights.HilbertSamuel.ClosedPtGenUniform.proof s14 s18 s19 s20
  have s22 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenNearCover.proof s14
  have s23 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenerationOfH1Vanishing.proof s21 s22
  have s24 := GroundTheory.Heights₂.Heights.HilbertSamuel.KleimanVarietyH1Generation.proof (PositivityTheory.KAmp.kAmp) s13 s23
  have s25 := GroundTheory.Heights₂.Heights.Kleiman.KHCechMapDeg.full
  have s26 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep.proof s11 s25
  have s27 := GroundTheory.Heights₂.Heights.HilbertSamuel.H1GenerationDevissage.proof s8 s11 s12 s26
  have s28 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenerationOfH1GenAmple.full
  have s29 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.proof
  have s30 := GroundTheory.Heights₂.Heights.Kleiman.KHFreeEmbed.full
  have s31 := GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp.full
  have s32 := GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep.full
  have s33 := GroundTheory.Heights₂.Heights.Kleiman.KHCombContract.full
  have s34 := GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic.proof s33
  have s35 := GroundTheory.Heights₂.Heights.Kleiman.KHFreeBadFinite.full
  have s36 := GroundTheory.Heights₂.Heights.Kleiman.KHTheoremSFree.proof s30 s31 s32 s33 s34 s35
  have s37 := GroundTheory.Heights₂.Heights.Kleiman.KHTheoremS.proof s36 s11 s8
  have s38 := GroundTheory.Heights₂.Heights.HilbertSamuel.QuotPartGraded.proof
  have s39 := GroundTheory.Heights₂.Heights.HilbertSamuel.KoszulCechComplex.proof
  have s40 := GroundTheory.Heights₂.Heights.HilbertSamuel.KoszulCechExact.proof
  have s41 := GroundTheory.Heights₂.Heights.HilbertSamuel.DoubleComplexVanish.proof
  have s42 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenKoszulStep.proof s39 s40 s41 s9 s10
  have s43 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistVanish.proof s37 s38 s42
  have s44 := GroundTheory.Heights₂.Heights.HilbertSamuel.AmpleOfGenTwist.proof s29 s43
  have s45 := GroundTheory.Heights₂.Heights.HilbertSamuel.KleimanScheme.proof s24 s27 s28 s44
  have s46 := GroundTheory.Heights₂.Heights.Targets.existsUniqueAll
  have s47 := GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleFibre.proof s45 (fun K _ ι _ => GroundTheory.Heights₂.Heights.geoNumStatement ι) s46
  have s48 := GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombLimit.full
  have s49 := GroundTheory.Heights₂.Heights.HilbertSamuel.G2.proof s4 s5 s6 s7 s47 s48
  have s50 := GroundTheory.Heights₂.Heights.HilbertSamuel.LiftSpread.proof
  have s51 := GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedPow.proof
  have s52 := GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionComplex.proof
  have s53 := GroundTheory.Heights₂.Heights.HilbertSamuel.ZeroCocycleSection.proof
  have s54 := GroundTheory.Heights₂.Heights.HilbertSamuel.SecCochReduce.proof
  have s55 := GroundTheory.Heights₂.Heights.HilbertSamuel.FibreSectionLift.proof s37 s38 s9 s10 s52 s53 s54
  have s56 := GroundTheory.Heights₂.Heights.HilbertSamuel.FibreRelLift.proof
  have s57 := GroundTheory.Heights₂.Heights.HilbertSamuel.LiftAtPrime.proof s51 s55 s56
  have s58 := GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.full
  have s59 := GroundTheory.Heights₂.Heights.HilbertSamuel.LiftModel.proof s50 s57 s58
  have s60 := GroundTheory.Heights₂.Heights.HilbertSamuel.ResVolume.proof
  have s61 := GroundTheory.Heights₂.Heights.Targets.LiftGraphPoints.proof
  have s62 := GroundTheory.Heights₂.Heights.AutoClose.Targets_LiftGraphMetric
  have s63 := GroundTheory.Heights₂.Heights.Targets.LiftBlockDatum.proof (GlobalTheory.T.resolution_exists_of_resolution_statement hResK) s60 s61 s62
  have s64 := GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists (GlobalTheory.T.resolution_exists_of_resolution_statement hResK)
  have s65 := GroundTheory.Heights₂.Heights.Inter.RatR.proof s64
  have s66 := GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance.proof s65
  have s67 := GroundTheory.Heights₂.Heights.HilbertSamuel.AddBlockIsometric.proof
  have s68 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockTop.proof ((GlobalTheory.T.degree_and_coordinates_of_resolution (GlobalTheory.T.resolution_exists_of_resolution_statement hResK)).2) s66 s67
  have s69 := GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundCount.full
  have s70 := GroundTheory.Heights₂.Heights.Targets.LiftCountAlongMultiples.proof s63 s68 (PositivityTheory.LocalParametersCuspidal.MB.HSM.theoremHSMBlock hAIS hResK) s69 (GlobalTheory.T.packing')
  have s71 := GroundTheory.Heights₂.Heights.Targets.AmpleCountAlongMultiples.proofAmple s59 s70
  have s72 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.proof (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS))
  have s73 := GroundTheory.Heights₂.Heights.Targets.NefBigCountAlongMultiples.proof s49 s71 s7 s72 (GlobalTheory.T.packing')
  have s74 := GroundTheory.Heights₂.Heights.Targets.AmpleCountAlongMultiples.statementB s73 (GlobalTheory.T.packing')
  have s75 := GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedProductNonneg.full
  have s76 := GroundTheory.Heights₂.Heights.HilbertSamuel.KleimanNefF.proof (PositivityTheory.KAmp.kAmp) s75
  have s77 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegAmple.full
  have s78 := GroundTheory.Heights₂.Heights.HilbertSamuel.NefPlusAmpleDegree.proof s76 s77
  have s79 := GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftNefBig.proof (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS)) s78
  have s80 := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.full
  have s81 := GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftSectionSeparation.proof (hAIS) hDBH s80
  have s82 := GroundTheory.Heights₂.Heights.HilbertSamuel.SecEq.proof
  have s83 := GroundTheory.Heights₂.Heights.HilbertSamuel.Conductor.proof s82
  have s84 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionLatticeFinite.proof s83
  have s85 := GroundTheory.Heights₂.Heights.HilbertSamuel.SeparatedSmallCount.proof s84
  have s86 := PositivityTheory.Pf1.MbRank.ShiftVolumeBound.of_ais s81 s85 (hAIS)
  have s87 := GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftIntersectionPolynomial.full
  have s88 := GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftDegreePolynomial.full
  have s89 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeDegreeZero.proof s74 s79 s86 s87 s88
  have s90 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeBig.proof s74 s89
  have s91 := GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert.proof
  have s92 := GroundTheory.Heights₂.Heights.Targets.CurveSectionQuotFinite.proof
  have s93 := GroundTheory.Heights₂.Heights.Targets.CurveRingFinite.proof
  have s94 := GroundTheory.Heights₂.Heights.Targets.CurveClosedPointChart.proof
  have s95 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointChart.proof s93 s94
  have s96 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointInj.proof s95
  have s97 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointSurj.proof s93 s94
  have s98 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointNagata.proof s95
  have s99 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointMultChart.proof s95 s98
  have s100 := GroundTheory.Heights₂.Heights.Targets.CurveSectionQuotLocal.proof
  have s101 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointLength.proof s95 s96 s97 s99 s100
  have s102 := GroundTheory.Heights₂.Heights.Targets.CurveVertPointResidue.proof s94
  have s103 := GroundTheory.Heights₂.Heights.Targets.CurveVertIndex.proof s92 s101 s102
  have s104 := GroundTheory.Heights₂.Heights.Targets.LocalGenFamily.proof
  have s105 := GroundTheory.Heights₂.Heights.Targets.LocallyPrincipalCoprimeField.proof
  have s106 := GroundTheory.Heights₂.Heights.Targets.InvertibleProductRep.proof
  have s107 := GroundTheory.Heights₂.Heights.Targets.InvertibleIndexCharP.proof
  have s108 := GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMul.proof s104 s105 s106 s107
  have s109 := GroundTheory.Heights₂.Heights.Targets.CurveIndexLinear.proof s93 s94 s108
  have s110 := GroundTheory.Heights₂.Heights.Targets.CurveBoxSmall.proof
  have s111 := GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.proof
  have s112 := GroundTheory.Heights₂.Heights.Targets.CurveFieldNumber.proof s111
  have s113 := GroundTheory.Heights₂.Heights.Targets.CurveEmbedOrbit.proof
  have s114 := GroundTheory.Heights₂.Heights.Targets.ChartLatFull.proof
  have s115 := GroundTheory.Heights₂.Heights.Targets.NumberFieldBoxCount.proof_closed
  have s116 := GroundTheory.Heights₂.Heights.Targets.CurveBoxLattice.proof s112 s113 s114 s115 s84
  have s117 := GroundTheory.Heights₂.Heights.Targets.CurveBoxCount.proof s110 s116
  have s118 := GroundTheory.Heights₂.Heights.Targets.CurveCountLower.proof s91 s103 s109 s117
  have s119 := GroundTheory.Heights₂.Heights.Targets.MoriwakiBigCurve.proof s118 (GlobalTheory.T.packing')
  have s120 := GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralAgainstPositive.full
  have s121 := GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNef.proof s76
  have s122 := GroundTheory.Heights₂.Heights.HilbertSamuel.MixedKleimanLow.proof s120 s121
  have s123 := GroundTheory.Heights₂.Heights.HilbertSamuel.ScaledFSHProps.proof
  have s124 := GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombExpand.full
  have s125 := GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.full
  have s126 := GroundTheory.Heights₂.Heights.HilbertSamuel.G4.proof s90 s125
  have s127 := GroundTheory.Heights₂.Heights.HilbertSamuel.CurveSmallCountLower.proof s91 s103 s109 s117
  have s128 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeBigDimensionOne.proof (GlobalTheory.T.packing') s127
  have s129 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeDimensionOne.proof s128
  have s130 := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionMixed.proof s126 s129 (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS)) s78
  have s131 := GroundTheory.Heights₂.Heights.HilbertSamuel.MixedSectionStep.proof s130 s65 s120 s121 s124
  have s132 := GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive.full
  have s133 := GroundTheory.Heights₂.Heights.HilbertSamuel.FSGeomDegPos.proof (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS) s132
  have s134 := GroundTheory.Heights₂.Heights.HilbertSamuel.ScaledFSTopPos.proof s133
  have s135 := GroundTheory.Heights₂.Heights.HilbertSamuel.MixedTopAlgebra.full
  have s136 := GroundTheory.Heights₂.Heights.HilbertSamuel.MixedKleimanTop.proof s123 s124 s131 s134 s135
  have s137 := GroundTheory.Heights₂.Heights.HilbertSamuel.MixedKleiman.proof s122 s136
  have s138 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithKleiman.proof s137
  have s139 := GroundTheory.Heights₂.Heights.HilbertSamuel.SuccessiveMinimaSpan.full
  have s140 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionPointValue.proof
  have s141 := GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeComplexRadical.proof
  have s142 := GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexMinimalPrimesContract.proof
  have s143 := GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexFormsOnPoints.proof s141 s142
  have s144 := GroundTheory.Heights₂.Heights.HilbertSamuel.IndependentModBaseChange.proof
  have s145 := GroundTheory.Heights₂.Heights.HilbertSamuel.RealFormsOnPoints.proof s143 s144
  have s146 := GroundTheory.Heights₂.Heights.HilbertSamuel.L2GramLattice.proof
  have s147 := GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsRankBound.full
  have s148 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionL2Lattice.proof s140 s145 s146 s147 s3
  have s149 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSpanStep.full
  have s150 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionRingFinite.proof s84 s149
  have s151 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockVeronese.proof s150
  have s152 := GroundTheory.Heights₂.Heights.HilbertSamuel.GenOnFibres.full
  have s153 := GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedRestrict.full
  have s154 := GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedNefGeneric.proof s152 s153 s75
  have s155 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerHeightsirational.proof s154 (GlobalTheory.T.kodaira_generic_of_ample_section_count (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.1 (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.2) s2
  have s156 := GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.proof
  have s157 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockArith.proof s156
  have s158 := GroundTheory.Heights₂.Heights.HilbertSamuel.LeviLogFlat.proof
  have s159 := GroundTheory.Heights₂.Heights.HilbertSamuel.LeviHolPerturb.proof
  have s160 := GroundTheory.Heights₂.Heights.HilbertSamuel.LeviCompHol.proof
  have s161 := GroundTheory.Heights₂.Heights.HilbertSamuel.LeviFSInvariant.proof
  have s162 := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionNormSqExtension.proof s158 s159 s160 s161
  have s163 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.proof s162
  have s164 := GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.full
  have s165 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockPointNorm.proof s140 s164
  have s166 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockOldPartSurj.proof
  have s167 := GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeZariskiDense.proof s143 s141 s142
  have s168 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMeasure.proof s165 s166 s167
  have s169 := GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockDatum.proof (GlobalTheory.T.resolution_exists_of_resolution_statement hResK) s60 s151 s155 s157 s163 s168
  have s170 := GroundTheory.Heights₂.Heights.HilbertSamuel.BlockChiCovolume.proof
  have s171 := GroundTheory.Heights₂.Heights.HilbertSamuel.TensorPowerL2Degree.proof s169 s68 s170 (PositivityTheory.LocalParametersCuspidal.MB.HSM.theoremHSMBlock hAIS hResK)
  have s172 := GroundTheory.Heights₂.Heights.HilbertSamuel.EuclideanSectionsPower.proof s148 s171
  have s173 := GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero.proof
  have s174 := GroundTheory.Heights₂.Heights.Targets.SublatticeDegree.full
  have s175 := GroundTheory.Heights₂.Heights.HilbertSamuel.EuclideanSections.proof s172 s173 s174 s139
  have s176 := GroundTheory.Heights₂.Heights.HilbertSamuel.G7.proof s139 s175
  have s177 := GroundTheory.Heights₂.Heights.HilbertSamuel.MonomialShift.proof (GlobalTheory.T.packing')
  have s178 := GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbMonomial.full
  have s179 := GroundTheory.Heights₂.Heights.HilbertSamuel.UpperNormalisation.proof s176 (GlobalTheory.T.packing') s83
  have s180 := GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeNef.proof s177 s178 s179
  exact ⟨s90, s119, s138, s176, s180⟩

theorem moriwakiBig_of_classicalTheorems (hResK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) (hAIS : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement)
    (hDBH : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.DenseBoundedHeight.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement :=
  GroundTheory.Heights₂.Heights.Targets.MoriwakiBig.of_found (hsChain hResK hAIS hDBH).1 (hsChain hResK hAIS hDBH).2.1

def HSUse : Prop :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ArithKleiman.Statement ∧ GroundTheory.Heights₂.Heights.HilbertSamuel.G7.Statement ∧
    GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeNef.Statement

theorem hsUse_of_hypotheses (hResK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) (hAIS : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement)
    (hDBH : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.DenseBoundedHeight.Statement) : HSUse :=
  (hsChain hResK hAIS hDBH).2.2

end PositivityTheory.Pf1.HilbertSamuelMoriwaki
