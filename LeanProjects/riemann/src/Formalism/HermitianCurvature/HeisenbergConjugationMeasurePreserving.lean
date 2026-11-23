import Formalism.HermitianCurvature.HermitianCurvatureProofs.SharpRecursion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecText
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BoxOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Minors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualVolumePowerIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferProductMonic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalingExponentIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleSS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondKernelPropertyKernel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AntidiagMulDiagonal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstEmbeddingOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Herglotz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualIdealInclusion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinorScalingLawGeneral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FacSuccOfNotMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Markov
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MiddleThirdEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cauchy
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HerglotzLowerSemicontinuous
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionCriticalPoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelGrowthBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RowNormSquareBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProductFactorBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AffineChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TripleForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RemainderNormLeStrictUpper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerBlockPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardCharacterExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevExtremalPolynomials
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnitaryInvariantGaussian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussianHessianIntegral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousInvUpper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralZeroFrequencyInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CharacterOrthogonalityDual
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ColumnOperationTripleForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AddedBlockKernelSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelPropertiesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonSummationDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeEqualityFromTestFunctions
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopDegreePolynomials
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplitPrimeToDifferent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LagrangeExtraction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationTypedIndependentExponent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwistedIsRealOrderLattice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordLiftInduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationScaledIdealMemIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordMonicExtraction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalConditionsAndQuotientSplitting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block32EqZeroOfUnipotent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReductionSurjective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalVolumePositivity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemIntegralGlOfMiddleBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrderChainWeights
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetLiftSquareRoot
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointwiseStabiliserParametrisationBijective
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OffDiagonalSchurComplement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramConjugationNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplitFrameTransitive
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointSetConstantMembership
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTopBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelExplicitFormula
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrderIndexAndStrata
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveSemidefinitePullback
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelInequality
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameLevelIndices
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelProperties
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormDomination
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictOrthogonalComplementNondeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinitePointSets
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelCoefficients
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MassRatioFormula
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockStartPoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelInequalitySplitBySize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondEmbedMulFirstEmbedApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmRingIdempotentUnitRatioIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaFactorisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CentreBlockStructure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LatticeAverageIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VandermondeRatioHarmonic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KroneckerEmbedMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFrameCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryAOfPropositionA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondVanishingOffRing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteOfEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EntryCommuteTransposedRMatrix
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaBOfComponents
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMatrixTransferConjTransposeCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumInvSqLeSub
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QEFirstMulSecondEqSwap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SixteenMulLeTwoPow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CriticalThresholdLowerBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialFlipCommuteDiagScalarOfFree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferMatrixFactorization
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaBoundOnBoundary
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordsAssembleHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordStatementsAllHold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2RmatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakApproximationGL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PlusLetterFrameOfData
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusLetterFrameOfData
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ResidueForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussFormMinusLetter
import Formalism.HermitianCurvature.HermitianCurvatureProofs.L0ConstantPartCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2OfFourEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CuspidalIrreducibleSubrep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FourierUniquenessMirabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WhittakerVanishingImpliesZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitTailEstimates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionDerivatives
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommuteLevelZeroElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StationaryPhaseEstimates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbedLoweringConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StationaryPhaseModel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EtaleIntegralityFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarScaling
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselScaling
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormBallVolumes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialMeansOrthogonal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermExpansionOfSteps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChangeOfVariablesXy
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumSwap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionWithDensities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealPowerIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanPositiveSemidefinite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteClassesPositiveSums
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragedVectorChoices
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralLatticeRefinementIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HessianScalingIntegrals
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanNormSquaredBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModulusLocallyConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensitySumsAndDomination
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EqZeroOfIdealCompact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramKernelHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragedKernelSums
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PosSemidefEntryBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdicNeighbourhood
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianLeviVectorBaseOrthogonal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermSumLattices
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussIndexIndependentOfChoice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelScalingBack
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussSumModulusOfLattice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoBlockPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubmoduleMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PadicChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsdFormConjRewrite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupremumAIsMajorant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HenselRootsBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThresholdBelowOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OutsideSystemsBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AxiomsFromFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonJointFirstReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JointInstanceTheoremA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevToThreshold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionGivesUniformBoundsForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PullLatticeTypedUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermExpansionMatrixFunction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GrowthOfBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelNablaStarRelations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MultiplicationOpHom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelWordsAssemble
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingConstantEqNablaStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GammaFamilyCommuteGenerators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferRtt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightedSumDifferenceIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerLevelsSameScalar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentBlockMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelLevelMultiplier
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetTopConvergence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EnergyEstimateFromParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivedCoefficientIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakToStrongSmoothnessReal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactlySupportedBanachModel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCellsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxPIRttLevel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CasimirEigenvalueCoefficients
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Truncated
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RttUpperRelationsFromDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Plain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainAndRowSums
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockEstimatesSumForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanBoundsLimits
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantIntegrals
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairingTriangular
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DeterminantGeneric
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LatticeSummability
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AverageOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondPolynomialClauses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialTheoremsAssembly
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameIntegralJacobian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScaleThresholdCharacters
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmegaNormCofactorOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TorusArgumentMultiplicative
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThresholdExponentEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RhoAntitoneOfInterlacing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DbarConjugationWeight
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RootPushforwardDensity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EigenvalueInterlacing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FibreExpansionZeroFails
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerDensityThreshold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragingVanishes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramProductIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualKernelLemmas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealWeightedForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliTwoByTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QRadialDecompositionOfPieces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfCVUnderIntOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordKeyIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNormalization
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordIntegralScaling
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOpenDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichRhoAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOrbitSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroEstimateProduct
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstNormRealNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConcreteBoundOfRecursion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFourthCondition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RelevantMonotoneOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerAntidiagonalExact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialDegreeExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialTheoremCorollary
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDiagonalMap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermVectorIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.XiYZhatIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorsCommuteTranslations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceLastLevel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliDetAdInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfUnitWords
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Sq2UnitOfEqOneOfSq2EqDiv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetClassEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiscMeanValue
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InverseSplitting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UpperMinorIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DetSubmatrixUnitriangularEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeDivOfMulEqLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormEntryBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SectionDecompositionOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearChangeOfVariablesBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatNormBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedFrameProperty
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JacobianAeNonzero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FourthWeightDensityOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeRulesA1
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExponentWordRecursion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShearMeasurability
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleCDerivatives
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftToRightConversion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialMapProper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerPairs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SectionDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MirrorDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConnectionRaisingConstantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsAuxiliaryXi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WittOrthonormalBasis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdCountLemmaVariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictedDualKernel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterpolationInverseMatrixSumIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealInputsBuiltClosedForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfCauchySchwarz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopOfLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalNormNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralFormulaPassesToLimits
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGHead
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopPSD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBJoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBTAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCFinal

namespace Formalism.FourierDecayAlt.Final

theorem recursionSharp : Formalism.FourierDecayAlt.RecursionSharp := Formalism.FourierDecayAlt.P.sharp_recursion
theorem recursionText : Formalism.FourierDecayAlt.RecursionText := Formalism.FourierDecayAlt.P.coarseBound
theorem boxSumOne : Formalism.FourierDecayAlt.BoxSumOne := Formalism.FourierDecayAlt.P.box_weights_sum_to_one
theorem leadingMinorsCount : Formalism.FourierDecayAlt.LeadingMinorsCount := Formalism.FourierDecayAlt.P.leading_minors_count
theorem dualSizeIdentity : Formalism.FourierDecayAlt.DualSizeIdentity := by
  intro ι _ c g rd r i hg hrd
  have hk : ((2 * r : ℤ) + 3 - 2 * i) = -((2 * i : ℤ) - 3 - 2 * r) := by ring
  have he : ((2 * r + 2 : ℤ) - 2 * ((i : ℤ) - 1)) = 1 - ((2 * i : ℤ) - 3 - 2 * r) := by ring
  rw [hk, he]
  generalize ((2 * i : ℤ) - 3 - 2 * r) = k
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  generalize Fintype.card ι = N
  have hg0 : g ≠ 0 := hg.ne'
  have hr0 : rd ≠ 0 := hrd.ne'
  rw [← zpow_natCast ((2 * Real.pi / g) ^ k), ← zpow_mul, mul_zpow, ← zpow_mul,
    show (-k) * (-(N : ℤ)) = k * N by ring, show (1 - k) * (N : ℤ) = N - k * N by ring,
    zpow_sub₀ hg0, zpow_neg, div_zpow, div_zpow]
  have h1 : (2 * Real.pi) ^ (k * (N : ℤ)) ≠ 0 := zpow_ne_zero _ (by positivity)
  have h2 : g ^ (k * (N : ℤ)) ≠ 0 := zpow_ne_zero _ hg0
  have h3 : rd ^ (k * (N : ℤ)) ≠ 0 := zpow_ne_zero _ hr0
  have h4 : g ^ (N : ℤ) ≠ 0 := zpow_ne_zero _ hg0
  field_simp
theorem mainConstant : Formalism.FourierDecayAlt.MainConstant := by
  intro P _ glk uk nn gg ρ₀ ρ₀' dimπ dimπ' V₀ deg hglk huk hnn hgg hV hdeg
  have key : ∏ p, (glk p / uk p) * (glk p * nn p) / gg p =
      (∏ p, glk p / uk p) * (∏ p, glk p / uk p) / ∏ p, gg p / (nn p * uk p) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    have h1 := (huk p).ne'
    have h2 := (hnn p).ne'
    have h3 := (hgg p).ne'
    field_simp
  have hG : 0 < ∏ p, gg p / (nn p * uk p) :=
    Finset.prod_pos (fun p _ => div_pos (hgg p) (mul_pos (hnn p) (huk p)))
  rw [key]
  have h4 := hG.ne'
  have h5 := hV.ne'
  have h6 := hdeg.ne'
  field_simp
theorem omNorm : Formalism.FourierDecayAlt.OmNorm := by
  intro V _ _ ip hadd hsmul hconj z x T T' Dr hT hz hx
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have huz : ip (x + (ip x z / (T : ℂ)) • z) z = 0 := by
    rw [hadd, hsmul, hz, div_mul_eq_mul_div, mul_neg, neg_div, mul_div_assoc, div_self hT0,
      mul_one, add_neg_cancel]
  have hzu : ip z (x + (ip x z / (T : ℂ)) • z) = 0 := by
    rw [hconj (x + (ip x z / (T : ℂ)) • z) z, huz, map_zero]
  have hxu : ip x (x + (ip x z / (T : ℂ)) • z) =
      starRingEnd ℂ (-(T' : ℂ) + ip x z / (T : ℂ) * starRingEnd ℂ (ip x z)) := by
    rw [hconj (x + (ip x z / (T : ℂ)) • z) x, hadd, hsmul, hx, hconj x z]
  have huu : ip (x + (ip x z / (T : ℂ)) • z) (x + (ip x z / (T : ℂ)) • z) =
      starRingEnd ℂ (-(T' : ℂ) + ip x z / (T : ℂ) * starRingEnd ℂ (ip x z)) := by
    rw [hadd x, hsmul, hxu, hzu, mul_zero, add_zero]
  refine ⟨by rw [hsmul, huz, mul_zero], ?_⟩
  rw [hsmul, hconj (Dr • (x + (ip x z / (T : ℂ)) • z)) (x + (ip x z / (T : ℂ)) • z), hsmul, huu,
    map_mul, Complex.conj_conj]
  push_cast
  rw [Complex.normSq_mul]
  push_cast
  rw [← Complex.mul_conj, ← Complex.mul_conj]
  field_simp
  ring
theorem interlaceSign : Formalism.FourierDecayAlt.I.InterlaceSign := Formalism.FourierDecayAlt.P.interlacing_sign
theorem qPositive : Formalism.FourierDecayAlt.I.QPositive := Formalism.FourierDecayAlt.P.q_positive_interlacing
theorem interlaceRatio : Formalism.FourierDecayAlt.I.InterlaceRatio := Formalism.FourierDecayAlt.P.interlacing_ratio
theorem selfDualG : Formalism.FourierDecayAlt.I.SelfDualG := by
  intro F _ o q hq hq0 a
  constructor
  · intro h
    have h1 := h (q, 0) (by
      simp only [Formalism.FourierDecayAlt.I.orderR, Set.mem_setOf_eq]
      exact ⟨hq, o.zero_mem, 1, o.one_mem, by ring⟩)
    have h2 := h (0, -q) (by
      simp only [Formalism.FourierDecayAlt.I.orderR, Set.mem_setOf_eq]
      exact ⟨o.zero_mem, o.neg_mem hq, 1, o.one_mem, by ring⟩)
    have h3 := h (1, 1) (by
      simp only [Formalism.FourierDecayAlt.I.orderR, Set.mem_setOf_eq]
      exact ⟨o.one_mem, o.one_mem, 0, o.zero_mem, by ring⟩)
    dsimp only at h1 h2 h3
    rw [mul_zero, sub_zero, mul_div_assoc, div_self hq0, mul_one] at h1
    rw [mul_zero, zero_sub, mul_neg, neg_neg, mul_div_assoc, div_self hq0, mul_one] at h2
    rw [mul_one, mul_one] at h3
    simp only [Formalism.FourierDecayAlt.I.orderR, Set.mem_setOf_eq]
    exact ⟨h1, h2, (a.1 - a.2) / q, h3, by field_simp <;> ring⟩
  · intro ha b hb
    simp only [Formalism.FourierDecayAlt.I.orderR, Set.mem_setOf_eq] at ha hb
    obtain ⟨ha1, ha2, t, ht, hat⟩ := ha
    obtain ⟨hb1, hb2, s, hs, hbs⟩ := hb
    have key : (a.1 * b.1 - a.2 * b.2) / q = a.1 * s + t * b.2 := by
      rw [div_eq_iff hq0]
      linear_combination a.1 * hbs + b.2 * hat
    rw [key]
    exact o.add_mem (o.mul_mem ha1 hs) (o.mul_mem ht hb2)
theorem tProdMonic : Formalism.FourierDecayAlt.I.TProdMonic := Formalism.FourierDecayAlt.P.transfer_product_monic
theorem ruleInv : Formalism.FourierDecayAlt.R.RuleInv := Formalism.FourierDecayAlt.P.inverseCommutators
theorem minorScale : Formalism.FourierDecayAlt.X.MinorScale := Formalism.FourierDecayAlt.P.minor_scaling_law
theorem scaleExponents : Formalism.FourierDecayAlt.X.ScaleExponents := Formalism.FourierDecayAlt.P.scaling_exponent_identities
theorem germPowers : Formalism.FourierDecayAlt.X.GermPowers := Formalism.FourierDecayAlt.P.germ_power_identity
theorem slicePowers : Formalism.FourierDecayAlt.X.SlicePowers := Formalism.FourierDecayAlt.P.slice_power_identity
theorem weightExponent : Formalism.FourierDecayAlt.X.WeightExponent := Formalism.FourierDecayAlt.P.weight_exponent_identity
theorem ruleSS : Formalism.FourierDecayAlt.R.RuleSS := Formalism.FourierDecayAlt.P.intertwinerConjugation
theorem levelOneKernelPoint_true : Formalism.FourierDecayAlt.A.LevelOneKernelPoint := Formalism.FourierDecayAlt.P.second_kernel_property_one
theorem levelOneKernelPair_true : Formalism.FourierDecayAlt.A.LevelOneKernelPair := Formalism.FourierDecayAlt.P.second_kernel_property_kernel
theorem ruleG : Formalism.FourierDecayAlt.R.RuleG := Formalism.FourierDecayAlt.P.gaugeConjugation
theorem ruleD : Formalism.FourierDecayAlt.R.RuleD := Formalism.FourierDecayAlt.P.shiftConjugation
theorem bigCellFree : Formalism.FourierDecayAlt.K.BigCellFree := Formalism.FourierDecayAlt.P.big_cell_free
theorem jointTheoremA : Formalism.FourierDecayAlt.K.JointTheoremA := Formalism.FourierDecayAlt.P.joint_theorem_A'
theorem wordFusion : Formalism.FourierDecayAlt.W.WordFusion := Formalism.FourierDecayAlt.P.word_fusion
theorem normLower : Formalism.FourierDecayAlt.W.NormLower := Formalism.FourierDecayAlt.P.norm_lower_bound
theorem herglotzZd : Formalism.FourierDecayAlt.H.HerglotzZd := Formalism.FourierDecayAlt.P.herglotz_Zd
theorem dual_g3 : Formalism.FourierDecayAlt.L.DualLatticeInclusion := Formalism.FourierDecayAlt.P.dual_third_group_holds
theorem dual_ideal_inclusion : Formalism.FourierDecayAlt.L.DualIdealInclusion := Formalism.FourierDecayAlt.P.dual_third_group_ideal
theorem minorScaleGen : Formalism.FourierDecayAlt.X.MinorScaleGen := Formalism.FourierDecayAlt.P.minor_scaling_law_general
theorem herglotzFejerZd : Formalism.FourierDecayAlt.H.HerglotzFejerZd := Formalism.FourierDecayAlt.P.herglotz_fejer_Zd
theorem aMarkov : Formalism.FourierDecayAlt.E.AMarkov := Formalism.FourierDecayAlt.P.markov_inequality
theorem markovVector : Formalism.FourierDecayAlt.E.MarkovVector := Formalism.FourierDecayAlt.P.markov_inequality_vector
theorem middleThird : Formalism.FourierDecayAlt.E.MiddleThird := Formalism.FourierDecayAlt.P.middle_third_estimate
theorem meanPosDef : Formalism.FourierDecayAlt.E.MeanPosDef := Formalism.FourierDecayAlt.P.mean_matrix_posDef
theorem cauchyTheta : Formalism.FourierDecayAlt.E.CauchyTheta := Formalism.FourierDecayAlt.P.cauchy_theta_identity
theorem herglotzLSC : Formalism.FourierDecayAlt.E.HerglotzLSC := Formalism.FourierDecayAlt.P.herglotz_lower_semicontinuous
theorem g_g0Deriv : Formalism.FourierDecayAlt.G.PhaseFunctionDeriv := Formalism.FourierDecayAlt.P.phase_function_deriv
theorem g_g0Crit : Formalism.FourierDecayAlt.G.PhaseFunctionCritical := Formalism.FourierDecayAlt.P.phase_function_critical_points
theorem g_hessCrit : Formalism.FourierDecayAlt.G.HessCrit := Formalism.FourierDecayAlt.P.hessian_at_critical
theorem g_hessDet : Formalism.FourierDecayAlt.G.HessDet := by
  intro m z
  rw [Matrix.det_smul, Fintype.card_fin]
  have hJ : (1 + Matrix.of fun _ _ => (1 : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).det =
      (m : ℂ) + 2 := by
    have e : (Matrix.of fun _ _ => (1 : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
        Matrix.replicateCol (Fin 1) (fun _ : Fin (m + 1) => (1 : ℂ)) *
          Matrix.replicateRow (Fin 1) (fun _ : Fin (m + 1) => (1 : ℂ)) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [e]
    have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1)
      (fun _ : Fin (m + 1) => (1 : ℂ)) (fun _ : Fin (m + 1) => (1 : ℂ))
    first | rw [h] | erw [h] | simp only [h]
    simp [dotProduct] <;> ring
  rw [hJ]
  ring
theorem g_gradSmall : Formalism.FourierDecayAlt.G.GradSmall := Formalism.FourierDecayAlt.P.gradient_small_near_critical
theorem g_gradLower : Formalism.FourierDecayAlt.G.GradLower := Formalism.FourierDecayAlt.P.gradient_lower_bound
theorem g_rootSetSpec : Formalism.FourierDecayAlt.G.RootSetSpec := Formalism.FourierDecayAlt.P.root_set_characterization
theorem g_leadingConstant : Formalism.FourierDecayAlt.G.LeadingConstant := Formalism.FourierDecayAlt.P.stationary_leading_constant
theorem g_dimCount : Formalism.FourierDecayAlt.G.DimCount := Formalism.FourierDecayAlt.P.dimension_count
theorem g_charAdditive : Formalism.FourierDecayAlt.G.CharAdditive := by
  intro n p q
  refine ⟨fun hp hq => ?_, fun hp hq => ?_⟩
  · obtain ⟨hp1, hp0⟩ := hp
    obtain ⟨hq1, hq0⟩ := hq
    simp only [Formalism.FourierDecayAlt.G.superSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_apply, Fintype.sum_eq_add i.castSucc i.succ]
    · rw [hp1, hq1]
      ring
    · exact ne_of_lt Fin.castSucc_lt_succ
    · intro k hk
      rcases lt_or_gt_of_ne hk.1 with h | h
      · rw [hp0 _ _ h, zero_mul]
      · have h1 : (i.castSucc : ℕ) < (k : ℕ) := h
        rw [Fin.coe_castSucc] at h1
        have h2 : (k : ℕ) ≠ (i.succ : ℕ) := fun e => hk.2 (Fin.ext e)
        rw [Fin.val_succ] at h2
        have h3 : i.succ < k := by
          show ((i.succ : Fin (n + 1)) : ℕ) < (k : ℕ)
          rw [Fin.val_succ]
          omega
        rw [hq0 _ _ h3, mul_zero]
  · obtain ⟨hp1, hp0⟩ := hp
    obtain ⟨hq1, hq0⟩ := hq
    simp only [Matrix.transpose_apply] at hp1 hp0 hq1 hq0
    simp only [Formalism.FourierDecayAlt.G.subSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_apply, Fintype.sum_eq_add i.castSucc i.succ]
    · rw [hp1, hq1]
      ring
    · exact ne_of_lt Fin.castSucc_lt_succ
    · intro k hk
      rcases lt_or_gt_of_ne hk.1 with h | h
      · rw [hq0 _ _ h, mul_zero]
      · have h1 : (i.castSucc : ℕ) < (k : ℕ) := h
        rw [Fin.coe_castSucc] at h1
        have h2 : (k : ℕ) ≠ (i.succ : ℕ) := fun e => hk.2 (Fin.ext e)
        rw [Fin.val_succ] at h2
        have h3 : i.succ < k := by
          show ((i.succ : Fin (n + 1)) : ℕ) < (k : ℕ)
          rw [Fin.val_succ]
          omega
        rw [hp0 _ _ h3, zero_mul]
theorem g_detOrbit : Formalism.FourierDecayAlt.G.DetOrbit := Formalism.FourierDecayAlt.P.det_orbit
theorem g_detMatch : Formalism.FourierDecayAlt.G.DetMatch := Formalism.FourierDecayAlt.P.det_weyl_matrix
theorem g_entriesM : Formalism.FourierDecayAlt.G.EntriesM := Formalism.FourierDecayAlt.P.matrix_entries
theorem g_shapeM : Formalism.FourierDecayAlt.G.ShapeM := Formalism.FourierDecayAlt.P.shape_of_matrix
theorem g_phaseFormula : Formalism.FourierDecayAlt.G.PhaseFormula := Formalism.FourierDecayAlt.P.phase_formula
theorem g_psiChar : Formalism.FourierDecayAlt.G.PsiChar := by
  intro β x y
  refine ⟨?_, ?_, ?_⟩
  · simp only [Formalism.FourierDecayAlt.G.psi, mul_add, Complex.add_re, Complex.ofReal_add, Complex.exp_add]
  · simp only [Formalism.FourierDecayAlt.G.psi]
    rw [mul_comm]
    first
    | exact Complex.norm_exp_ofReal_mul_I _
    | simp [Complex.norm_exp_ofReal_mul_I]
  · simp [Formalism.FourierDecayAlt.G.psi]
theorem g_psiNormalisations : Formalism.FourierDecayAlt.G.PsiNormalisations := by
  intro w
  have h1 : ((4 * (Real.pi : ℂ) * w).re) = 4 * Real.pi * w.re := by
    simp [Complex.mul_re] <;> ring
  have h2 : ((-2 * Complex.I * w).re) = 2 * w.im := by
    simp [Complex.mul_re] <;> ring
  refine ⟨?_, ?_⟩
  · simp only [Formalism.FourierDecayAlt.G.psi, h1, Complex.add_conj]
    congr 1
    push_cast
    ring
  · simp only [Formalism.FourierDecayAlt.G.psi, h2, Complex.sub_conj]
    congr 1
    push_cast
    ring
theorem level_recursion_ls : Formalism.FourierDecayAlt.F7.LevelRecursionLS := Formalism.FourierDecayAlt.P.level_recursion_lower_sum
theorem level_recursion : Formalism.FourierDecayAlt.F7.LevelRecursion := Formalism.FourierDecayAlt.P.levelRecursion_statement
theorem level_recursion_condition_needed : Formalism.FourierDecayAlt.F7.LevelRecursionCondNeeded := Formalism.FourierDecayAlt.P.levelRecursionCondNeeded_statement
theorem choice_of_constants_consistent : Formalism.FourierDecayAlt.F7.ChoiceOfConstants := by
  intro C₁ CE C' C Θ Kx f r hC₁ hCE hf hKx h8 h12 hC'Θ hΘ hr
  have hΘpos : 0 < Θ := by linarith
  have hf0 : f ≠ 0 := by omega
  have hC₁Θ : C₁ / Θ ≤ 1 / 8 := by rw [div_le_iff₀ hΘpos]; linarith
  have hsumΘ : (C₁ + CE) / Θ ≤ 1 / 8 := by rw [div_le_iff₀ hΘpos]; linarith
  have hCEΘ : CE / Θ ≤ 1 / 8 := by rw [div_le_iff₀ hΘpos]; linarith
  have p1 : 0 ≤ C₁ / Θ := by positivity
  have p2 : 0 ≤ CE / Θ := by positivity
  have hadd : C₁ / Θ + CE / Θ = (C₁ + CE) / Θ := by rw [add_div]
  have hE : CE * Θ ^ (-(Kx - 5 / 2)) ≤ CE / Θ := by
    have h := Real.rpow_le_rpow_of_exponent_le hΘ (show -(Kx - 5 / 2) ≤ (-1 : ℝ) by linarith)
    rw [Real.rpow_neg_one] at h
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h hCE.le
  have hE0 : 0 ≤ CE * Θ ^ (-(Kx - 5 / 2)) := by positivity
  have ha : (C₁ / Θ) ^ f ≤ (1 / 8) ^ f := by gcongr
  have hb : (C₁ / Θ) ^ f ≤ 1 / 8 :=
    le_trans ha (pow_le_of_le_one (by norm_num) (by norm_num) hf0)
  have hc : (CE * Θ ^ (-(Kx - 5 / 2))) ^ f ≤ (CE / Θ) ^ f := by
    gcongr <;> first | exact hE | positivity
  have s1 : (CE / Θ) ^ f ≤ ((C₁ + CE) / Θ) ^ f := by gcongr <;> linarith
  have s2 : (C₁ / Θ) ^ f ≤ ((C₁ + CE) / Θ) ^ f := by gcongr <;> linarith
  have hd : (CE * Θ ^ (-(Kx - 5 / 2))) ^ f + 2 * (C₁ / Θ) ^ f ≤ 3 * ((C₁ + CE) / Θ) ^ f := by
    linarith
  have t1 : (CE / Θ) ^ f ≤ CE / Θ := pow_le_of_le_one p2 (by linarith) hf0
  have t2 : (C₁ / Θ) ^ f ≤ C₁ / Θ := pow_le_of_le_one p1 (by linarith) hf0
  have hsmall : (CE * Θ ^ (-(Kx - 5 / 2))) ^ f + 2 * (C₁ / Θ) ^ f ≤ 1 / 4 := by linarith
  have hS0 : 0 ≤ ((C₁ + CE) / Θ) ^ f := by positivity
  have hdiv : 12 * ((C₁ + CE) / Θ) ≤ C / Θ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hpow : (12 * ((C₁ + CE) / Θ)) ^ f ≤ (C / Θ) ^ f := by
    gcongr <;> first | exact hdiv | positivity
  rw [mul_pow] at hpow
  have h12f : (12 : ℝ) ^ 1 ≤ 12 ^ f := by gcongr <;> first | norm_num | omega
  rw [pow_one] at h12f
  have hrS : (r : ℝ) * (12 * ((C₁ + CE) / Θ) ^ f) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left
      (le_trans (mul_le_mul_of_nonneg_right h12f hS0) hpow) (Nat.cast_nonneg r)) hr
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  refine ⟨ha, hb, hc, hd, ?_⟩
  calc ((r : ℝ) + 1) * ((CE * Θ ^ (-(Kx - 5 / 2))) ^ f + 2 * (C₁ / Θ) ^ f)
      = (r : ℝ) * ((CE * Θ ^ (-(Kx - 5 / 2))) ^ f + 2 * (C₁ / Θ) ^ f) +
          ((CE * Θ ^ (-(Kx - 5 / 2))) ^ f + 2 * (C₁ / Θ) ^ f) := by ring
    _ ≤ (r : ℝ) * (3 * ((C₁ + CE) / Θ) ^ f) + 1 / 4 :=
        add_le_add (mul_le_mul_of_nonneg_left hd hr0) hsmall
    _ ≤ 1 / 2 := by nlinarith [hrS]
theorem theorem_a_constants : Formalism.FourierDecayAlt.F7.TheoremAConstants := Formalism.FourierDecayAlt.P.constants_of_theorem_A
theorem schurTwo_true : Formalism.FourierDecayAlt.F7.SchurTwo := Formalism.FourierDecayAlt.P.schur_two_factor_bound
theorem schur_test_on_lattice : Formalism.FourierDecayAlt.F7.SchurLattice := Formalism.FourierDecayAlt.P.schur_lattice_bound
theorem schur_words : Formalism.FourierDecayAlt.F7.SchurWords := Formalism.FourierDecayAlt.P.schur_word_bound
theorem wordWeight_true : Formalism.FourierDecayAlt.F7.WordWeight := by
  intro K _ q x w Y hw
  induction w with
  | nil => simp [Formalism.FourierDecayAlt.F7.qW, Formalism.FourierDecayAlt.F7.xW]
  | cons l w ih =>
    have hl := hw l (by simp)
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    simp only [Formalism.FourierDecayAlt.F7.qW, Formalism.FourierDecayAlt.F7.xW, List.map_cons, List.prod_cons]
    rw [mul_div_mul_comm, ih']
    unfold Formalism.FourierDecayAlt.F7.OffPoles at hl
    unfold Formalism.FourierDecayAlt.F7.wFactor
    rcases l with ⟨pl, pt, fi⟩
    cases pl
    · cases fi
      · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
        rw [div_one]
        ring
      · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
        have b1 : pt - Y - 1 ≠ 0 := fun h => hl.1 (by linear_combination h)
        have b2 : pt - (Y + 1) - 1 ≠ 0 := fun h => hl.2 (by linear_combination h)
        have b3 : pt - (Y + 1) ≠ 0 := fun h => hl.1 (by linear_combination h)
        field_simp <;> ring
    · cases fi
      · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
        rw [div_one]
        ring
      · simp only [Bool.false_eq_true, ↓reduceIte] at hl ⊢
        have a1 : Y - pt ≠ 0 := hl.1
        have a2 : Y - pt + 1 ≠ 0 := fun h => hl.2 (by linear_combination h)
        have e1 : Y + 1 - pt - 1 = Y - pt := by ring
        have e2 : Y + 1 - pt = Y - pt + 1 := by ring
        rw [e1, e2, div_self (div_ne_zero a2 a1)]
        ring
theorem plus_unchanged : Formalism.FourierDecayAlt.F7.PlusUnchanged := by
  intro K _ q x w Y hw hpf
  rw [wordWeight_true K q x w Y hw]
  have h1 : (w.map fun l => Formalism.FourierDecayAlt.F7.wFactor l Y).prod = 1 := by
    apply List.prod_eq_one
    intro a ha
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    simp [Formalism.FourierDecayAlt.F7.wFactor, (hpf l hl).1, (hpf l hl).2]
  rw [h1, mul_one]
theorem all_first_weight : Formalism.FourierDecayAlt.F7.AllFirstWeight := Formalism.FourierDecayAlt.P.all_first_level_weight
theorem weight_bounds_first_order : Formalism.FourierDecayAlt.F7.WeightBounds := Formalism.FourierDecayAlt.P.word_weight_bounds
theorem first_order_weight_bounds_all : Formalism.FourierDecayAlt.F7.AllFirstBounds := Formalism.FourierDecayAlt.P.all_first_level_bounds
theorem g_selfDual : Formalism.FourierDecayAlt.G.SelfDual := Formalism.FourierDecayAlt.P.self_dual_measure
theorem g_selfDualUnique : Formalism.FourierDecayAlt.G.SelfDualUnique := Formalism.FourierDecayAlt.P.self_dual_measure_unique
theorem g_affineChange : Formalism.FourierDecayAlt.G.AffineChange := Formalism.FourierDecayAlt.P.affine_change_of_variables
theorem g_scalePi : Formalism.FourierDecayAlt.G.ScalePi := Formalism.FourierDecayAlt.P.scale_product_measure
theorem g_germOfRate : Formalism.FourierDecayAlt.G.GermOfRate := Formalism.FourierDecayAlt.P.germ_of_rate
theorem iso_zz_is_iso : Formalism.FourierDecayAlt.A5.IsoZZIsIso := Formalism.FourierDecayAlt.P.matchingIsoSetEq
theorem lambda_last : Formalism.FourierDecayAlt.A5.LamLast := Formalism.FourierDecayAlt.P.invRowFunctionalLast
theorem isomorphism_class_count : Formalism.FourierDecayAlt.A5.IsoCount := Formalism.FourierDecayAlt.P.matchingIsoCount
theorem triple_form_identity : Formalism.FourierDecayAlt.A5.TripleForm := Formalism.FourierDecayAlt.P.tripleForm
theorem g_cornerRelation : Formalism.FourierDecayAlt.G.CornerRelation := Formalism.FourierDecayAlt.P.corner_relation
theorem g_cornerSplit : Formalism.FourierDecayAlt.G.CornerSplit := Formalism.FourierDecayAlt.P.corner_split
theorem g_cofLead : Formalism.FourierDecayAlt.G.CofLead := Formalism.FourierDecayAlt.P.leading_cofactor
theorem g_rho1Limit : Formalism.FourierDecayAlt.G.Rho1Limit := Formalism.FourierDecayAlt.P.first_coordinate_limit
theorem g_cofLower : Formalism.FourierDecayAlt.G.CofLower := Formalism.FourierDecayAlt.P.cofactor_lower_bound
theorem g_stabLong : Formalism.FourierDecayAlt.G.StabLong := Formalism.FourierDecayAlt.P.stabilizer_long_point
theorem g_sectionLong : Formalism.FourierDecayAlt.G.SectionLong := Formalism.FourierDecayAlt.P.section_at_long_point
theorem g_stabBlock : Formalism.FourierDecayAlt.G.StabBlock := Formalism.FourierDecayAlt.P.stabilizer_block_point
theorem g_sectionBlock : Formalism.FourierDecayAlt.G.SectionBlock := Formalism.FourierDecayAlt.P.section_at_block_point
theorem g_g1Crit : Formalism.FourierDecayAlt.G.CornerEntryCritical := Formalism.FourierDecayAlt.P.reduced_phase_critical_points
theorem g_limitShape : Formalism.FourierDecayAlt.G.LimitShape := Formalism.FourierDecayAlt.P.limit_shape
theorem g_limitMatrix : Formalism.FourierDecayAlt.G.LimitMatrix := Formalism.FourierDecayAlt.P.limit_matrix
theorem g_limitIntegral : Formalism.FourierDecayAlt.G.LimitIntegral := Formalism.FourierDecayAlt.P.limit_integral
theorem b_lemmaBFromSteps : Formalism.FourierDecayAlt.B.LemmaBFromSteps := Formalism.FourierDecayAlt.P.bessel_lemma_from_reductions
theorem b_assembleAdj : Formalism.FourierDecayAlt.B.AssembleAdj := Formalism.FourierDecayAlt.P.adjointness_of_bessel_transform
theorem b_assemblePoly : Formalism.FourierDecayAlt.B.AssemblePoly := Formalism.FourierDecayAlt.P.adjointness_polynomially_bounded
theorem b_jtauOne : Formalism.FourierDecayAlt.B.JtauOne := Formalism.FourierDecayAlt.P.bessel_function_trivial_index
theorem b_dilBigCell : Formalism.FourierDecayAlt.B.DilBigCell := Formalism.FourierDecayAlt.P.dilation_big_cell_formula
theorem b_dilMem : Formalism.FourierDecayAlt.B.DilMem := Formalism.FourierDecayAlt.P.dilation_mem_group
theorem b_lemmaBClosedFromParts : Formalism.FourierDecayAlt.B.LemmaBClosedFromParts := Formalism.FourierDecayAlt.P.bessel_lemma_closed_form
theorem chebyshev_sharp : Formalism.FourierDecayAlt.F7.ChebSharp := Formalism.FourierDecayAlt.P.chebyshev_bound_sharp
theorem chebyshev_coefficient_value : Formalism.FourierDecayAlt.F7.ChebCoValue := Formalism.FourierDecayAlt.P.chebyshev_coeff_value
theorem chebyshev_attained : Formalism.FourierDecayAlt.F7.ChebAttained := Formalism.FourierDecayAlt.P.chebyshev_bound_attained
theorem chebyshev_leading_coefficient_bound : Formalism.FourierDecayAlt.F7.ChebLeadBound := Formalism.FourierDecayAlt.P.chebyshev_leading_coeff_bound
theorem chebyshev_node_spacing : Formalism.FourierDecayAlt.F7.ChebSpacing := Formalism.FourierDecayAlt.P.chebyshevNodeSpacing_true
theorem equicontinuity : Formalism.FourierDecayAlt.F7.EquiCo := Formalism.FourierDecayAlt.P.equioscillation_coeff
theorem equicontinuity_bound : Formalism.FourierDecayAlt.F7.EquiCoBound := Formalism.FourierDecayAlt.P.equioscillation_coeff_bound
theorem g_gaussOneDamped : Formalism.FourierDecayAlt.G.GaussOneDamped := Formalism.FourierDecayAlt.P.gaussian_one_damped
theorem g_gaussOne : Formalism.FourierDecayAlt.G.GaussOne := Formalism.FourierDecayAlt.P.gaussian_one_dim
theorem g_gaussMultiOfOne : Formalism.FourierDecayAlt.G.GaussMultiOfOne := Formalism.FourierDecayAlt.P.gaussian_multi_of_one
theorem g_gaussHessOfMulti : Formalism.FourierDecayAlt.G.GaussHessOfMulti := Formalism.FourierDecayAlt.P.gaussian_hessian_of_multi
theorem g_unitaryInvariant : Formalism.FourierDecayAlt.G.UnitaryInvariant := Formalism.FourierDecayAlt.P.unitary_invariant_gaussian
theorem g_takagi : Formalism.FourierDecayAlt.G.Takagi := Formalism.FourierDecayAlt.P.takagi_factorization
theorem g_gaussMulti : Formalism.FourierDecayAlt.G.GaussMulti := Formalism.FourierDecayAlt.P.gaussian_multi_integral
theorem g_gaussHess : Formalism.FourierDecayAlt.G.GaussHess := Formalism.FourierDecayAlt.P.gaussian_hessian_integral
theorem g_quotientMeasure : Formalism.FourierDecayAlt.G.QuotientMeasure := Formalism.FourierDecayAlt.P.quotient_measure
theorem g_jacobian : Formalism.FourierDecayAlt.G.Jacobian := Formalism.FourierDecayAlt.P.jacobian_formula
theorem b_seminormIneq : Formalism.FourierDecayAlt.B.SeminormIneq := Formalism.FourierDecayAlt.P.seminorm_inequality
theorem b_polarisation : Formalism.FourierDecayAlt.B.Polarisation := by
  intro V _ _ W β γ hβ hγ hd x hx y hy
  have pol : ∀ δ : V → V → ℂ, Formalism.FourierDecayAlt.B.IsSesq δ → ∀ u v : V,
      4 * δ u v = δ (u + v) (u + v) - δ (u + (-1 : ℂ) • v) (u + (-1 : ℂ) • v) +
        Complex.I * δ (u + Complex.I • v) (u + Complex.I • v) -
        Complex.I * δ (u + (-Complex.I) • v) (u + (-Complex.I) • v) := by
    intro δ hδ u v
    obtain ⟨h1, h2, h3, h4⟩ := hδ
    simp only [h1, h2, h3, h4, map_neg, map_one, Complex.conj_I]
    linear_combination (2 * (δ u v - δ v u)) * Complex.I_sq
  have m1 : ∀ c : ℂ, x + c • y ∈ W := fun c => W.add_mem hx (W.smul_mem c hy)
  have key : 4 * β x y = 4 * γ x y := by
    rw [pol β hβ x y, pol γ hγ x y, hd _ (W.add_mem hx hy), hd _ (m1 (-1)), hd _ (m1 Complex.I),
      hd _ (m1 (-Complex.I))]
  exact mul_left_cancel₀ (by norm_num) key
theorem b_formCoreC : Formalism.FourierDecayAlt.B.FormCoreC := Formalism.FourierDecayAlt.P.bilinear_form_continuity
theorem b_formCore : Formalism.FourierDecayAlt.B.FormCore := Formalism.FourierDecayAlt.P.bilinear_form_at_zero
theorem b_fatouParam : Formalism.FourierDecayAlt.B.FatouParam := Formalism.FourierDecayAlt.P.fatou_lemma_in_parameter
theorem b_regIBP : Formalism.FourierDecayAlt.B.RegIBP := Formalism.FourierDecayAlt.P.integration_by_parts_regularised
theorem b_testDecay : Formalism.FourierDecayAlt.B.TestDecay := Formalism.FourierDecayAlt.P.test_function_decay
theorem b_intRdZeroInv : Formalism.FourierDecayAlt.B.IntRdZeroInv := Formalism.FourierDecayAlt.P.integral_zero_frequency_invariant
theorem dualSpan_true : Formalism.FourierDecayAlt.A5.DualSpan := Formalism.FourierDecayAlt.P.dualSpan_true_hc
theorem endomorphism_kr : Formalism.FourierDecayAlt.A5.EndKR := Formalism.FourierDecayAlt.P.quotientEndScalar
theorem character_orthogonality_dual : Formalism.FourierDecayAlt.A5.CharOrthDual := Formalism.FourierDecayAlt.P.characterOrthogonalityDual
theorem character_orthogonality : Formalism.FourierDecayAlt.A5.CharOrth := Formalism.FourierDecayAlt.P.characterOrthogonality
theorem unramified_relative : Formalism.FourierDecayAlt.S6.UnramRelative := Formalism.FourierDecayAlt.P.unramRelative
theorem field_extension_degree_facts : Formalism.FourierDecayAlt.S6.DegreeFacts := Formalism.FourierDecayAlt.P.degreeFacts_statement
theorem local_ordinary : Formalism.FourierDecayAlt.S6.LocOrdinary := Formalism.FourierDecayAlt.P.localAwayFromLevel
theorem local_twisted_lattice : Formalism.FourierDecayAlt.S6.LocTw := Formalism.FourierDecayAlt.P.localTwistedLattice
theorem ideal_norm_formula : Formalism.FourierDecayAlt.S6.NormIdl := Formalism.FourierDecayAlt.P.scaledIdealNorm
theorem discriminant_square : Formalism.FourierDecayAlt.S6.DiscrSquare := Formalism.FourierDecayAlt.P.discrSquare
theorem between_lattices : Formalism.FourierDecayAlt.S6.Between := Formalism.FourierDecayAlt.P.twistedLatticeBetween
theorem ideals_match : Formalism.FourierDecayAlt.S6.IdealsMatch := Formalism.FourierDecayAlt.P.dualIdealEqLiftIdeal
theorem text_from_general : Formalism.FourierDecayAlt.S6.TextFromGeneral := Formalism.FourierDecayAlt.P.periodLatticeFactsSplitOfGeneral
theorem inverse_last_column : Formalism.FourierDecayAlt.A5.InvLastCol := Formalism.FourierDecayAlt.P.inverse_last_column_formula
theorem tt_end : Formalism.FourierDecayAlt.A5.TTEnd := Formalism.FourierDecayAlt.P.triple_form_end_identity
theorem column_operation : Formalism.FourierDecayAlt.A5.ColOp := Formalism.FourierDecayAlt.P.column_operation_identity
theorem column_operation_on_rows : Formalism.FourierDecayAlt.A5.ColOpRow := Formalism.FourierDecayAlt.P.column_operation_row_form
theorem column_operation_triple : Formalism.FourierDecayAlt.A5.ColOpTriple := Formalism.FourierDecayAlt.P.column_operation_triple_form
theorem tt_recursion : Formalism.FourierDecayAlt.A5.TTStep := Formalism.FourierDecayAlt.P.triple_form_recursion
theorem integral_quotient_finite : Formalism.FourierDecayAlt.A5.IntFinite := Formalism.FourierDecayAlt.P.integral_points_finite
theorem parahoric_quotient_finite : Formalism.FourierDecayAlt.A5.KpFinite := Formalism.FourierDecayAlt.P.kernel_quotient_finite
theorem gramIdentity_true : Formalism.FourierDecayAlt.A5.GramIdentity := Formalism.FourierDecayAlt.P.gram_kernel_identity
theorem parahoric_gram_matrix : Formalism.FourierDecayAlt.A5.KpGram := Formalism.FourierDecayAlt.P.kernel_gram_property
theorem ns_support : Formalism.FourierDecayAlt.A5.NsSupport := Formalism.FourierDecayAlt.P.added_block_kernel_support
theorem zero_level_ones_vector : Formalism.FourierDecayAlt.A5.BaseKernelOne := Formalism.FourierDecayAlt.P.zero_kernel_all_ones
theorem padic_datum_properties : Formalism.FourierDecayAlt.A5.DatumPadic := Formalism.FourierDecayAlt.P.padic_local_datum_facts
theorem blockKernelProperties_of_components : Formalism.FourierDecayAlt.A5.BlockKernelPropertiesOfSteps := Formalism.FourierDecayAlt.P.second_gram_vanishing_of_parts
theorem latticeAverage_of_gram : Formalism.FourierDecayAlt.A5.LemmaAAssemble := Formalism.FourierDecayAlt.P.lattice_average_lemma_from_parts
theorem singleBlock_of_components : Formalism.FourierDecayAlt.A5.SingleBlockOfSteps := Formalism.FourierDecayAlt.P.first_kernel_properties_of_hypotheses
theorem singleBlockTheta_of_components : Formalism.FourierDecayAlt.A5.SingleBlockThetaOfSteps := Formalism.FourierDecayAlt.P.first_theta_properties_of_parts
theorem poisson_summation_move : Formalism.FourierDecayAlt.F7.PoissonStep := Formalism.FourierDecayAlt.P.poisson_summation_level
theorem poisson_summation_decay : Formalism.FourierDecayAlt.F7.PoissonStepDecay := Formalism.FourierDecayAlt.P.poisson_level_decay
theorem poisson_summable : Formalism.FourierDecayAlt.F7.PoissonSummable := Formalism.FourierDecayAlt.P.poisson_series_summable
theorem product_of_decays_summable : Formalism.FourierDecayAlt.F7.ProductDecaySummable := Formalism.FourierDecayAlt.P.product_decay_summable
theorem poisson_summation_text : Formalism.FourierDecayAlt.F7.PoissonStepText := Formalism.FourierDecayAlt.P.poisson_summation_level_statement
theorem b_aeFromTests : Formalism.FourierDecayAlt.B.AeFromTests := Formalism.FourierDecayAlt.P.ae_equality_from_test_functions
theorem pairHighest_true : Formalism.FourierDecayAlt.F7.PairTop := Formalism.FourierDecayAlt.P.pairing_top_degree
theorem j_pairing : Formalism.FourierDecayAlt.F7.JPairing := Formalism.FourierDecayAlt.P.j_pairing_formula
theorem plane_wave_top : Formalism.FourierDecayAlt.F7.PlaneWaveTop := Formalism.FourierDecayAlt.P.plane_wave_top_degree
theorem liftHighest_true : Formalism.FourierDecayAlt.F7.LiftTop := Formalism.FourierDecayAlt.P.lift_top_degree
theorem dual_lattice_supset : Formalism.FourierDecayAlt.S6.DualSupset := Formalism.FourierDecayAlt.P.traceDualGe
theorem split_coprime : Formalism.FourierDecayAlt.S6.SplitCoprime := Formalism.FourierDecayAlt.P.splitPrimeToDifferent
theorem lagrange_leading_term : Formalism.FourierDecayAlt.F7.LagrangeLead := Formalism.FourierDecayAlt.P.lagrange_leading_coeff
theorem extraction_k : Formalism.FourierDecayAlt.F7.ExtractK := Formalism.FourierDecayAlt.P.extract_K_bound
theorem extraction_bound : Formalism.FourierDecayAlt.F7.ExtractBound := Formalism.FourierDecayAlt.P.extractBound_statement
theorem extraction_probability : Formalism.FourierDecayAlt.F7.ExtractProb := Formalism.FourierDecayAlt.P.extract_probability_bound
theorem dual_weights : Formalism.FourierDecayAlt.F7.DualWeights := by
  intro Ls _ ω N N' hω hN hN' hS
  have hS0 : (∑ L', ω L') ≠ 0 := hS.ne'
  constructor
  · have h : ∀ L, ω L / (2 * ∑ L', ω L') + ω L / (2 * ∑ L', ω L') = ω L / ∑ L', ω L' := by
      intro L
      field_simp <;> ring
    rw [Finset.sum_congr rfl (fun L _ => h L), ← Finset.sum_div, div_self hS0]
  · have key : ∀ L, ω L * √(N L * N' L) ≤ (∑ L', ω L') *
        (ω L / (2 * ∑ L', ω L') * N L + ω L / (2 * ∑ L', ω L') * N' L) := by
      intro L
      have e : (∑ L', ω L') * (ω L / (2 * ∑ L', ω L') * N L + ω L / (2 * ∑ L', ω L') * N' L) =
          ω L * ((N L + N' L) / 2) := by
        field_simp <;> ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (hω L)
      have h1 : N L * N' L ≤ ((N L + N' L) / 2) ^ 2 := by nlinarith [sq_nonneg (N L - N' L)]
      calc √(N L * N' L) ≤ √(((N L + N' L) / 2) ^ 2) := Real.sqrt_le_sqrt h1
        _ = (N L + N' L) / 2 := Real.sqrt_sq (by linarith [hN L, hN' L])
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun L _ => key L)
theorem extraction_chebyshev : Formalism.FourierDecayAlt.F7.ExtractCheb := Formalism.FourierDecayAlt.P.extract_chebyshev_bound
theorem local_lattice_typed_model : Formalism.FourierDecayAlt.S6.LocTyped := Formalism.FourierDecayAlt.P.localisation_typed_condition
theorem local_global_lattices : Formalism.FourierDecayAlt.S6.LocalGlobal := Formalism.FourierDecayAlt.P.local_global_principle
theorem covolumeIndex_true : Formalism.FourierDecayAlt.S6.CovolumeIndex := Formalism.FourierDecayAlt.P.covolumeIndex
theorem twist_is_f_lattice : Formalism.FourierDecayAlt.S6.TwIsFLattice := Formalism.FourierDecayAlt.P.twistedIsRealOrderLattice
theorem plane_wave_word_chebyshev : Formalism.FourierDecayAlt.F7.PlaneWaveWordCheb := Formalism.FourierDecayAlt.P.plane_wave_word_chebyshev_alt
theorem lift_of_chebyshev_word : Formalism.FourierDecayAlt.F7.LiftWordCheb := Formalism.FourierDecayAlt.P.lift_word_chebyshev
theorem power_conjugation_stable : Formalism.FourierDecayAlt.S6.PowConjStable := Formalism.FourierDecayAlt.P.different_power_conj_stable
theorem dual_lattice_containment : Formalism.FourierDecayAlt.S6.DualSubset := Formalism.FourierDecayAlt.P.dual_lattice_subset
theorem least_norm_vector_in_ideal_class : Formalism.FourierDecayAlt.S6.LeastNorm := Formalism.FourierDecayAlt.P.least_norm_in_ideal
theorem size_quotient : Formalism.FourierDecayAlt.S6.SizeQuotient := Formalism.FourierDecayAlt.P.size_quotient_identity
theorem assemble_least_norm : Formalism.FourierDecayAlt.S6.AssembleLeast := Formalism.FourierDecayAlt.P.assemble_least_norm_and_sizes
theorem local_lattices_combine : Formalism.FourierDecayAlt.S6.AssembleLocal := Formalism.FourierDecayAlt.P.assemble_local_conditions
theorem assemble_lattices : Formalism.FourierDecayAlt.S6.AssembleLattices := Formalism.FourierDecayAlt.P.assemble_lattice_facts
theorem typed_lattice_model : Formalism.FourierDecayAlt.S6.TypedModel := Formalism.FourierDecayAlt.P.typed_local_model
theorem plane_wave_word : Formalism.FourierDecayAlt.F7.PlaneWaveWord := Formalism.FourierDecayAlt.P.plane_wave_word_formula
theorem lift_word : Formalism.FourierDecayAlt.F7.LiftWord := Formalism.FourierDecayAlt.P.lift_word_formula
theorem lift_vector_of_word : Formalism.FourierDecayAlt.F7.LiftVectorWord := Formalism.FourierDecayAlt.P.lift_vector_word
theorem modular_multiplication : Formalism.FourierDecayAlt.A5.ModMul := Formalism.FourierDecayAlt.P.modulus_positive_multiplicative
theorem cokernel_cardinality_formula : Formalism.FourierDecayAlt.A5.CokerCard := Formalism.FourierDecayAlt.P.cokernel_card_inverse_modulus
theorem kp_block_diagonal : Formalism.FourierDecayAlt.A5.KpBlockDiag := Formalism.FourierDecayAlt.P.kernel_block_diagonal_by_modulus
theorem ns_block_diagonal : Formalism.FourierDecayAlt.A5.NsBlockDiag := Formalism.FourierDecayAlt.P.added_block_kernel_block_diagonal
theorem index_of_lattices : Formalism.FourierDecayAlt.S6.IndexCore := Formalism.FourierDecayAlt.P.twistedLatticeIndex
theorem g_omReduced : Formalism.FourierDecayAlt.G.OmReduced := Formalism.FourierDecayAlt.P.orbital_integral_reduced
theorem g_omConverges : Formalism.FourierDecayAlt.G.OmConverges := Formalism.FourierDecayAlt.P.orbital_integral_converges_abs
theorem lattices_general_position_bound : Formalism.FourierDecayAlt.S6.LatticesGeneral := Formalism.FourierDecayAlt.P.lattice_facts_general
theorem text_lattices : Formalism.FourierDecayAlt.S6.TextLattices := Formalism.FourierDecayAlt.P.lattice_facts_two_split_primes
theorem least_norm_text : Formalism.FourierDecayAlt.S6.TextLeast := Formalism.FourierDecayAlt.P.least_norm_and_size_quotient
theorem text_local : Formalism.FourierDecayAlt.S6.TextLocal := Formalism.FourierDecayAlt.P.local_conditions_and_quotient_splitting
theorem b_stepPhBound : Formalism.FourierDecayAlt.B.StepPhBound := Formalism.FourierDecayAlt.P.phase_function_bound
theorem b_stepRegPh : Formalism.FourierDecayAlt.B.StepRegPh := Formalism.FourierDecayAlt.P.regularised_pairing_via_phase
theorem b_stepPhAdj : Formalism.FourierDecayAlt.B.StepPhAdj := Formalism.FourierDecayAlt.P.phase_function_adjoint
theorem corner_minors_count : Formalism.FourierDecayAlt.S3.CornerMinorsCount := Formalism.FourierDecayAlt.P.cornerMinorsCount_true
theorem unit_stratum_coset_structure : Formalism.FourierDecayAlt.S3.UnitStratumCoset := Formalism.FourierDecayAlt.P.unit_stratum_coset
theorem unit_stratum_proportion : Formalism.FourierDecayAlt.S3.UnitStratumShare := Formalism.FourierDecayAlt.P.unit_stratum_share
theorem unit_stratum_mass_formula : Formalism.FourierDecayAlt.S3.UnitStratumMass := Formalism.FourierDecayAlt.P.unit_stratum_mass
theorem levelsExist_true : Formalism.FourierDecayAlt.S3.LevelsExist := Formalism.FourierDecayAlt.P.levels_exist'
theorem reduction_map_surjective_mod_p : Formalism.FourierDecayAlt.S3.ReductionOnto := Formalism.FourierDecayAlt.P.reductionOnto_statement
theorem index_kpp : Formalism.FourierDecayAlt.S3.IndexKpp := Formalism.FourierDecayAlt.P.corner_level_index
theorem iwahori_index_formula : Formalism.FourierDecayAlt.S3.IndexJH := Formalism.FourierDecayAlt.P.jordan_holder_index
theorem natural_parahoric_index : Formalism.FourierDecayAlt.S3.IndexKnat := Formalism.FourierDecayAlt.P.natural_level_index
theorem knat_product : Formalism.FourierDecayAlt.S3.KnatProduct := Formalism.FourierDecayAlt.P.natural_level_product
theorem parahoric_index_product_formula : Formalism.FourierDecayAlt.S3.KppProduct := Formalism.FourierDecayAlt.P.corner_level_product
theorem columns_true : Formalism.FourierDecayAlt.S3.Columns := Formalism.FourierDecayAlt.P.column_identity
theorem knat_gamma : Formalism.FourierDecayAlt.S3.KnatGamma := Formalism.FourierDecayAlt.P.middle_level_volume_index
theorem localProduct_true : Formalism.FourierDecayAlt.S3.LocalProduct := Formalism.FourierDecayAlt.P.local_ratio_product
theorem jacobian_of_change_of_variables_constant : Formalism.FourierDecayAlt.S3.JacobianConstant := Formalism.FourierDecayAlt.P.jacobian_natural_measure_constant
theorem signature_bound : Formalism.FourierDecayAlt.S3.SigBound := Formalism.FourierDecayAlt.P.form_signature_bound
theorem counting_theorem : Formalism.FourierDecayAlt.S3.MainTheorem := Formalism.FourierDecayAlt.P.mass_formula_constant_one
theorem displayed_d_star : Formalism.FourierDecayAlt.S3.DstarProductFormula := Formalism.FourierDecayAlt.P.dual_density_explicit_form
theorem displayed_n_n0 : Formalism.FourierDecayAlt.S3.NN0Formula := Formalism.FourierDecayAlt.P.density_explicit_form
theorem displayed_sum : Formalism.FourierDecayAlt.S3.VolumeMassSum := Formalism.FourierDecayAlt.P.density_final_sum
theorem typed_arithmetic : Formalism.FourierDecayAlt.S3.TypedArithmetic := Formalism.FourierDecayAlt.P.typedArithmetic_statement
theorem integral_product : Formalism.FourierDecayAlt.S3.IntegralProduct := Formalism.FourierDecayAlt.P.integralProduct_statement
theorem order_units : Formalism.FourierDecayAlt.S3.ROrderUnits := Formalism.FourierDecayAlt.P.order_unit_group
theorem order_self_dual : Formalism.FourierDecayAlt.S3.ROrderSelfDual := Formalism.FourierDecayAlt.P.rOrderSelfDual_statement
theorem chain_identity : Formalism.FourierDecayAlt.S3.ChainIdentity := Formalism.FourierDecayAlt.P.chain_weight_identity
theorem unit_heads_mass : Formalism.FourierDecayAlt.S3.UnitHeadsMass := Formalism.FourierDecayAlt.P.unitHeadsMass_statement
theorem b_dilN : Formalism.FourierDecayAlt.B.DilN := Formalism.FourierDecayAlt.P.dilation_unipotent_measure
theorem b_dilUW : Formalism.FourierDecayAlt.B.DilUW := Formalism.FourierDecayAlt.P.dilation_unipotent_weyl_measure
theorem b_cCLin : Formalism.FourierDecayAlt.B.CCLin := Formalism.FourierDecayAlt.P.matrix_coefficient_linear
theorem b_dilCC : Formalism.FourierDecayAlt.B.DilCC := Formalism.FourierDecayAlt.P.dilation_matrix_coefficient
theorem ta_oneLevelOfSteps : Formalism.FourierDecayAlt.TA.OneLevelOfSteps := Formalism.FourierDecayAlt.P.one_level_inequality_of_parts
theorem ta_reductionOfSteps : Formalism.FourierDecayAlt.TA.ReductionOfSteps := Formalism.FourierDecayAlt.P.reduction_bound_of_one_level
theorem b_stepClause : Formalism.FourierDecayAlt.B.StepClause := Formalism.FourierDecayAlt.P.clause_of_regularized_limit
theorem b_assembleEq : Formalism.FourierDecayAlt.B.AssembleEq := Formalism.FourierDecayAlt.P.assemble_equality_identity
theorem b_assembleDiag : Formalism.FourierDecayAlt.B.AssembleDiag := Formalism.FourierDecayAlt.P.assemble_diagonal_identity
theorem lduExists_true : Formalism.FourierDecayAlt.S3.LDUExists := Formalism.FourierDecayAlt.P.ldu_decomposition_exists
theorem lower_diagonal_upper_decomposition_unique : Formalism.FourierDecayAlt.S3.LDUUnique := Formalism.FourierDecayAlt.P.ldu_decomposition_unique
theorem leadInvariant_true : Formalism.FourierDecayAlt.S3.LeadInvariant := Formalism.FourierDecayAlt.P.lead_invariant_bis
theorem cornerInvariant_true : Formalism.FourierDecayAlt.S3.CornerInvariant := Formalism.FourierDecayAlt.P.corner_invariant_bis
theorem inverseCorner_true : Formalism.FourierDecayAlt.S3.InverseCorner := Formalism.FourierDecayAlt.P.inverse_corner_identity
theorem groups_are_groups : Formalism.FourierDecayAlt.S3.GroupsAreGroups := Formalism.FourierDecayAlt.P.level_groups_are_subgroups
theorem s_explicit : Formalism.FourierDecayAlt.S3.SExplicit := Formalism.FourierDecayAlt.P.frame_stabiliser_explicit
theorem unipotent_normalizer_explicit : Formalism.FourierDecayAlt.S3.NUExplicit := Formalism.FourierDecayAlt.P.unipotent_levi_explicit
theorem finite_group_cardinality_formula : Formalism.FourierDecayAlt.S3.CardN := Formalism.FourierDecayAlt.P.card_unipotent_radical
theorem cardS_true : Formalism.FourierDecayAlt.S3.CardS := Formalism.FourierDecayAlt.P.card_frame_stabiliser
theorem card_n_unipotent : Formalism.FourierDecayAlt.S3.CardNU := Formalism.FourierDecayAlt.P.card_unipotent_levi_product
theorem card_unipotent_k : Formalism.FourierDecayAlt.S3.CardUk := Formalism.FourierDecayAlt.P.card_unitary_levi
theorem gamma_product : Formalism.FourierDecayAlt.S3.GammaProduct := Formalism.FourierDecayAlt.P.gamma_factor_product
theorem stabiliserIndexFinite_true : Formalism.FourierDecayAlt.S3.StabiliserIndexFinite := Formalism.FourierDecayAlt.P.card_pointwise_stabiliser
theorem ta_offDiagSchur : Formalism.FourierDecayAlt.TA.OffDiagSchur := Formalism.FourierDecayAlt.P.off_diagonal_schur_complement
theorem ta_cosetsOne : Formalism.FourierDecayAlt.TA.CosetsOne := Formalism.FourierDecayAlt.P.cosets_last_block_size_one
theorem ta_cosetsS : Formalism.FourierDecayAlt.TA.CosetsS := Formalism.FourierDecayAlt.P.cosets_last_block_size_ge_two
theorem split_frame_count : Formalism.FourierDecayAlt.S3.SplitFrameCount := Formalism.FourierDecayAlt.P.s3_split_frame_count
theorem split_frame_density_formula : Formalism.FourierDecayAlt.S3.SplitFrameDensity := Formalism.FourierDecayAlt.P.split_frame_density
theorem split_frame_transitive : Formalism.FourierDecayAlt.S3.SplitFrameTransitive := Formalism.FourierDecayAlt.P.s3_split_frame_transitive
theorem ta_a4Limit : Formalism.FourierDecayAlt.TA.TopDominationLimit := Formalism.FourierDecayAlt.P.domination_limit
theorem ta_splitLast : Formalism.FourierDecayAlt.TA.SplitLast := Formalism.FourierDecayAlt.P.split_last_block
theorem ta_diagTop : Formalism.FourierDecayAlt.TA.DiagTop := Formalism.FourierDecayAlt.P.diagonal_top_block
theorem ta_diagCosets : Formalism.FourierDecayAlt.TA.DiagCosets := Formalism.FourierDecayAlt.P.diagonal_cosets
theorem ta_epsLimit : Formalism.FourierDecayAlt.TA.EpsLimit := Formalism.FourierDecayAlt.P.epsilon_limit
theorem singleBlockFormula_true : Formalism.FourierDecayAlt.A5.SingleBlockFormula := Formalism.FourierDecayAlt.P.first_kernel_explicit_formula
theorem s_is_frame_stabiliser : Formalism.FourierDecayAlt.S3.SIsFrameStabiliser := Formalism.FourierDecayAlt.P.frame_stabiliser_characterisation
theorem frameStabiliserPointwise_true : Formalism.FourierDecayAlt.S3.FrameStabiliserPointwise := Formalism.FourierDecayAlt.P.pointwise_stabiliser_characterisation
theorem frame_level_exists : Formalism.FourierDecayAlt.S3.FrameLevelExists := Formalism.FourierDecayAlt.P.frame_level_exists_alt
theorem parahoric_corner_index : Formalism.FourierDecayAlt.S3.KppCorner := Formalism.FourierDecayAlt.P.corner_group_index_explicit
theorem order_index : Formalism.FourierDecayAlt.S3.ROrderIndex := Formalism.FourierDecayAlt.P.order_index_alt
theorem unit_stratum_total : Formalism.FourierDecayAlt.S3.UnitStratumTotal := Formalism.FourierDecayAlt.P.unit_stratum_total_alt
theorem zero_level_count_from_mass : Formalism.FourierDecayAlt.S3.DensityFromMassFormula := Formalism.FourierDecayAlt.P.density_from_mass
theorem sharp_count : Formalism.FourierDecayAlt.S3.MainSharp := Formalism.FourierDecayAlt.P.mass_formula_sharp
theorem tb_splitBySize : Formalism.FourierDecayAlt.TB.SplitBySize := Formalism.FourierDecayAlt.P.splitByLastSize
theorem tb_diagStep : Formalism.FourierDecayAlt.TB.DiagStep := Formalism.FourierDecayAlt.P.diagStep
theorem ta_oneLevel : Formalism.FourierDecayAlt.TA.OneLevel := Formalism.FourierDecayAlt.P.one_level_inequality
theorem ta_theoremAReduction : Formalism.FourierDecayAlt.TA.TheoremAReduction := Formalism.FourierDecayAlt.P.theorem_a_reduction
theorem index_of_first_congruence_subgroup : Formalism.FourierDecayAlt.S3.CongruenceLevelIndex := Formalism.FourierDecayAlt.P.first_congruence_index
theorem frame_index : Formalism.FourierDecayAlt.S3.FrameIndex := Formalism.FourierDecayAlt.P.frameIndex_statement
theorem omega_stable : Formalism.FourierDecayAlt.S3.OmStable := Formalism.FourierDecayAlt.P.omStable_statement
theorem blockKernelPosSemidef_true : Formalism.FourierDecayAlt.A5.BlockKernelPosSemidef := Formalism.FourierDecayAlt.P.second_gram_property
theorem singleBlockPeriodic_true : Formalism.FourierDecayAlt.A5.SingleBlockPeriodic := Formalism.FourierDecayAlt.P.first_kernel_periodic
theorem singleBlockPosSemidef_true : Formalism.FourierDecayAlt.A5.SingleBlockPosSemidef := Formalism.FourierDecayAlt.P.first_kernel_gram_property
theorem singleBlockParseval_true : Formalism.FourierDecayAlt.A5.SingleBlockParseval := Formalism.FourierDecayAlt.P.first_kernel_parseval
theorem theta_equality_first : Formalism.FourierDecayAlt.A5.Th1Eq := Formalism.FourierDecayAlt.P.first_theta_kernel_equality
theorem singleBlockThetaProps_true : Formalism.FourierDecayAlt.A5.SingleBlockThetaProps := Formalism.FourierDecayAlt.P.first_theta_equals_first_kernel
theorem tb_oneStep : Formalism.FourierDecayAlt.TB.OneStep := Formalism.FourierDecayAlt.P.singleBlockStep
theorem tb_multiStep : Formalism.FourierDecayAlt.TB.MultiStep := Formalism.FourierDecayAlt.P.longBlockStep
theorem unitary_group_order_formula : Formalism.FourierDecayAlt.S3.UnitaryOrder := Formalism.FourierDecayAlt.P.unitary_group_order
theorem witt_hermitian : Formalism.FourierDecayAlt.S3.WittHerm := Formalism.FourierDecayAlt.P.witt_hermitian_frames
theorem tb_limitStep : Formalism.FourierDecayAlt.TB.LimitStep := Formalism.FourierDecayAlt.P.limitStep
theorem tb_oneLevelOfSteps : Formalism.FourierDecayAlt.TB.OneLevelOfSteps := Formalism.FourierDecayAlt.P.levelInequalityOfSteps
theorem tb_theoremAOfSteps : Formalism.FourierDecayAlt.TB.TheoremAOfSteps := Formalism.FourierDecayAlt.P.towerBoundOfSteps
theorem sz_sumRanks : Formalism.FourierDecayAlt.Sz.SumRanks := Formalism.FourierDecayAlt.P.sumRanks
theorem sz_levelExponent : Formalism.FourierDecayAlt.Sz.LevelExponent := Formalism.FourierDecayAlt.P.levelExponent
theorem sz_indexRatio : Formalism.FourierDecayAlt.Sz.IndexRatio := Formalism.FourierDecayAlt.P.indexRatio
theorem sz_factorialCancel : Formalism.FourierDecayAlt.Sz.FactorialCancel := Formalism.FourierDecayAlt.P.factorialCancel
theorem sz_volumeChain : Formalism.FourierDecayAlt.Sz.VolumeChain := Formalism.FourierDecayAlt.P.volumeChain
theorem sz_propA : Formalism.FourierDecayAlt.Sz.PropA := Formalism.FourierDecayAlt.P.massRatioFormula
theorem wd_insMul : Formalism.FourierDecayAlt.Wd.InsMul := Formalism.FourierDecayAlt.P.position_insertion_mul_compat
theorem wd_insStar : Formalism.FourierDecayAlt.Wd.InsStar := Formalism.FourierDecayAlt.P.position_insertion_star_compat
theorem wd_insDiag : Formalism.FourierDecayAlt.Wd.InsDiag := Formalism.FourierDecayAlt.P.position_insertion_diagonal_compat
theorem wd_insFree : Formalism.FourierDecayAlt.Wd.InsFree := Formalism.FourierDecayAlt.P.position_insertion_free_compat
theorem tb_schurStep : Formalism.FourierDecayAlt.TB.SchurStep := Formalism.FourierDecayAlt.P.schurRecursion_true
theorem tb_oneLevel : Formalism.FourierDecayAlt.TB.OneLevel := Formalism.FourierDecayAlt.P.one_level_inequality_split_by_size
theorem tb_theoremA : Formalism.FourierDecayAlt.TB.TheoremA := Formalism.FourierDecayAlt.P.sharp_recursion_theorem_a
theorem wd_exchPlus : Formalism.FourierDecayAlt.Wd.ExchPlus := Formalism.FourierDecayAlt.P.exchange_relation_plus
theorem wd_exchMinus : Formalism.FourierDecayAlt.Wd.ExchMinus := Formalism.FourierDecayAlt.P.exchange_relation_minus
theorem sz_dualLattice : Formalism.FourierDecayAlt.Sz.DualLattice := Formalism.FourierDecayAlt.P.dual_lattice_bound
theorem sz_gPowers : Formalism.FourierDecayAlt.Sz.GPowers := Formalism.FourierDecayAlt.P.g_power_bounds
theorem sz_normalisedForms : Formalism.FourierDecayAlt.Sz.NormalisedForms := Formalism.FourierDecayAlt.P.normalised_forms
theorem sz_placement : Formalism.FourierDecayAlt.Sz.Placement := Formalism.FourierDecayAlt.P.lattice_placement
theorem sz_thresholdProducts : Formalism.FourierDecayAlt.Sz.ThresholdProducts := Formalism.FourierDecayAlt.P.threshold_products
theorem sz_thetaLower : Formalism.FourierDecayAlt.Sz.ThetaLower := Formalism.FourierDecayAlt.P.theta_lower_bound
theorem sz_thetaPower : Formalism.FourierDecayAlt.Sz.ThetaPower := Formalism.FourierDecayAlt.P.theta_power_bound
theorem final_term_small_bound : Formalism.FourierDecayAlt.Sz.FinalSmall := Formalism.FourierDecayAlt.P.final_smallness
theorem sz_factorisation : Formalism.FourierDecayAlt.Sz.Factorisation := Formalism.FourierDecayAlt.P.betaFactorisation
theorem sz_nodeBound : Formalism.FourierDecayAlt.Sz.NodeBound := Formalism.FourierDecayAlt.P.nodeBound
theorem sz_firstBound : Formalism.FourierDecayAlt.Sz.FirstBound := Formalism.FourierDecayAlt.P.edgeFactorBound
theorem sz_positionBefore : Formalism.FourierDecayAlt.Sz.PositionBefore := Formalism.FourierDecayAlt.P.positionBefore
theorem sz_positionAfter : Formalism.FourierDecayAlt.Sz.PositionAfter := Formalism.FourierDecayAlt.P.positionAfter
theorem sz_positionAt : Formalism.FourierDecayAlt.Sz.PositionAt := Formalism.FourierDecayAlt.P.slotAt_true
theorem sz_positionTop : Formalism.FourierDecayAlt.Sz.PositionTop := Formalism.FourierDecayAlt.P.positionTop
theorem sz_positionProduct : Formalism.FourierDecayAlt.Sz.ProdOneAddTwoDivLeSqrt := Formalism.FourierDecayAlt.P.positionProduct
theorem sz_positionsBefore : Formalism.FourierDecayAlt.Sz.PositionsBefore := Formalism.FourierDecayAlt.P.positionsBefore
theorem forcing_true : Formalism.FourierDecayAlt.S3.Forcing := Formalism.FourierDecayAlt.P.block_forcing
theorem centre_blocks : Formalism.FourierDecayAlt.S3.CentreBlocks := Formalism.FourierDecayAlt.P.centre_block_structure
theorem centre_forcing : Formalism.FourierDecayAlt.S3.CentreForcing := Formalism.FourierDecayAlt.P.centreForcing_true
theorem stabiliser_trivial : Formalism.FourierDecayAlt.S3.StabiliserTrivial := Formalism.FourierDecayAlt.P.stabiliserTrivial_true
theorem lattice_average_bound_identity : Formalism.FourierDecayAlt.A5.AvgClaim := Formalism.FourierDecayAlt.P.lattice_average_identity
theorem sz_interlacing : Formalism.FourierDecayAlt.Sz.Interlacing := Formalism.FourierDecayAlt.P.interlacing
theorem sz_lamAnti : Formalism.FourierDecayAlt.Sz.LamAnti := Formalism.FourierDecayAlt.P.lamStrictAnti
theorem sz_harmonicVand : Formalism.FourierDecayAlt.Sz.HarmonicVand := Formalism.FourierDecayAlt.P.vandermondeRatioHarmonic
theorem sz_positionDiff : Formalism.FourierDecayAlt.Sz.PositionDiff := Formalism.FourierDecayAlt.P.positionDiff
theorem wd_positionRTTPlus : Formalism.FourierDecayAlt.Wd.PositionRTTPlus := Formalism.FourierDecayAlt.P.position_RTT_relation_plus
theorem wd_positionRTTMinus : Formalism.FourierDecayAlt.Wd.PositionRTTMinus := Formalism.FourierDecayAlt.P.position_RTT_relation_minus
theorem wd_startModule : Formalism.FourierDecayAlt.Wd.StartModule := Formalism.FourierDecayAlt.P.initial_module_structure
theorem hermitian_frame_count : Formalism.FourierDecayAlt.S3.HermFrameCount := Formalism.FourierDecayAlt.P.hermFrameCount_statement
theorem density_case_analysis : Formalism.FourierDecayAlt.S3.DensCases := Formalism.FourierDecayAlt.P.density_case_split
theorem ordinary_density_bound : Formalism.FourierDecayAlt.S3.DensOrdinaryBound := Formalism.FourierDecayAlt.P.density_ordinary_bound
theorem density_typed : Formalism.FourierDecayAlt.S3.DensTyped := Formalism.FourierDecayAlt.P.densTyped_statement
theorem typed_unit_check : Formalism.FourierDecayAlt.S3.TypedUnitCheck := Formalism.FourierDecayAlt.P.typed_unit_verification
theorem prime_tail : Formalism.FourierDecayAlt.S3.PrimeTail := Formalism.FourierDecayAlt.P.prime_tail_bound
theorem sz_zetaTail : Formalism.FourierDecayAlt.Sz.ZetaTail := Formalism.FourierDecayAlt.P.zeta_tail_bound
theorem sz_eaSize : Formalism.FourierDecayAlt.Sz.EaSize := Formalism.FourierDecayAlt.P.exponent_sizes
theorem sz_corA : Formalism.FourierDecayAlt.Sz.CorA := Formalism.FourierDecayAlt.P.corollary_a_of_proposition_a
theorem sz_bracketBound : Formalism.FourierDecayAlt.Sz.BracketBound := Formalism.FourierDecayAlt.P.bracket_bound_alt
theorem b_stepUnfold : Formalism.FourierDecayAlt.B.StepUnfold := Formalism.FourierDecayAlt.P.unfolding_identity_of_integration_formula
theorem b_stepJCont : Formalism.FourierDecayAlt.B.StepJCont := Formalism.FourierDecayAlt.P.orbital_integral_ae_convergence_continuity
theorem b_stepDilBeta : Formalism.FourierDecayAlt.B.StepDilBeta := Formalism.FourierDecayAlt.P.dilation_identity_of_jacobian
theorem blockKernelSupport_true : Formalism.FourierDecayAlt.A5.BlockKernelSupport := Formalism.FourierDecayAlt.P.second_vanishing_off_ring
theorem gram_determinant_dual_bound_a : Formalism.FourierDecayAlt.A5.A2 := Formalism.FourierDecayAlt.P.second_gram_and_vanishing
theorem wd_dualPlus : Formalism.FourierDecayAlt.Wd.DualPlus := Formalism.FourierDecayAlt.P.duality_plus
theorem wd_dualMinus : Formalism.FourierDecayAlt.Wd.DualMinus := Formalism.FourierDecayAlt.P.duality_minus
theorem b_stepRegBound : Formalism.FourierDecayAlt.B.StepRegBound := Formalism.FourierDecayAlt.P.regularized_beta_bound_continuity_sesquilinear
theorem b_stepRegAverage : Formalism.FourierDecayAlt.B.StepRegAverage := Formalism.FourierDecayAlt.P.regularised_average_identity
theorem exchange_e1 : Formalism.FourierDecayAlt.Wd.ExchangePlusFactor := Formalism.FourierDecayAlt.P.exchange_plus_factor
theorem exchange_e2 : Formalism.FourierDecayAlt.Wd.ExchangeMinusFactorStar := Formalism.FourierDecayAlt.P.exchange_second_case
theorem exchange_e3 : Formalism.FourierDecayAlt.Wd.ExchangeMinusFactorTranspose := Formalism.FourierDecayAlt.P.exchange_third_case
theorem exchange_e4 : Formalism.FourierDecayAlt.Wd.ExchangePlusFactorTranspose := Formalism.FourierDecayAlt.P.exchange_fourth_case
theorem b_lemmaB : Formalism.FourierDecayAlt.B.LemmaB := Formalism.FourierDecayAlt.P.lemma_B_of_components
theorem wd_siteStep : Formalism.FourierDecayAlt.Wd.SiteStep := Formalism.FourierDecayAlt.P.site_exchange_relation
theorem wd_xpFix : Formalism.FourierDecayAlt.Wd.XpFix := Formalism.FourierDecayAlt.P.positive_word_fixed
theorem wd_xmFix : Formalism.FourierDecayAlt.Wd.XmFix := Formalism.FourierDecayAlt.P.negative_word_fixed
theorem wd_entryOne : Formalism.FourierDecayAlt.Wd.EntryOne := Formalism.FourierDecayAlt.P.word_matrix_entry_one
theorem wd_exchVecA : Formalism.FourierDecayAlt.Wd.ExchVecA := Formalism.FourierDecayAlt.P.exchange_vector_positive
theorem wd_exchVecB : Formalism.FourierDecayAlt.Wd.ExchVecB := Formalism.FourierDecayAlt.P.exchange_vector_negative
theorem wd_cwEigen : Formalism.FourierDecayAlt.Wd.CwEigen := Formalism.FourierDecayAlt.P.conjugate_word_eigen
theorem wd_uwProduct : Formalism.FourierDecayAlt.Wd.UwProduct := Formalism.FourierDecayAlt.P.word_product_formula
theorem sz_vandNonTop : Formalism.FourierDecayAlt.Sz.VandNonTop := Formalism.FourierDecayAlt.P.vandermondeNonTop
theorem sz_vandTop : Formalism.FourierDecayAlt.Sz.VandTop := Formalism.FourierDecayAlt.P.vandermondeTop
theorem sz_edgeFactors : Formalism.FourierDecayAlt.Sz.EdgeFactors := Formalism.FourierDecayAlt.P.edgeFactors
theorem sz_edgeRatios : Formalism.FourierDecayAlt.Sz.EdgeRatios := Formalism.FourierDecayAlt.P.edgeRatios
theorem sz_vandWords : Formalism.FourierDecayAlt.Sz.VandWords := Formalism.FourierDecayAlt.P.vandermondeWords
theorem wd_rhUU : Formalism.FourierDecayAlt.Wd.RhUU := Formalism.FourierDecayAlt.P.R_matrix_UU_relation
theorem wd_rhtUU : Formalism.FourierDecayAlt.Wd.RhtUU := Formalism.FourierDecayAlt.P.transposed_R_matrix_UU_relation
theorem wd_planeWaveVec : Formalism.FourierDecayAlt.Wd.PlaneWaveVec := Formalism.FourierDecayAlt.P.plane_wave_vector_identity
theorem wd_planeWaveWord : Formalism.FourierDecayAlt.Wd.PlaneWaveWord := Formalism.FourierDecayAlt.P.plane_wave_word_identity
theorem wd_letterPlus : Formalism.FourierDecayAlt.Wd.LetterPlus := Formalism.FourierDecayAlt.P.letter_module_plus
theorem wd_letterMinus : Formalism.FourierDecayAlt.Wd.LetterMinus := Formalism.FourierDecayAlt.P.letter_module_minus
theorem sz_sizesMain : Formalism.FourierDecayAlt.Sz.SizesMain := Formalism.FourierDecayAlt.P.size_bounds_conclusion
theorem sz_tcritWords : Formalism.FourierDecayAlt.Sz.TcritWords := Formalism.FourierDecayAlt.P.critical_threshold_words
theorem sz_tWords : Formalism.FourierDecayAlt.Sz.TWords := Formalism.FourierDecayAlt.P.threshold_words
theorem sz_vandLamLower : Formalism.FourierDecayAlt.Sz.VandLamLower := Formalism.FourierDecayAlt.P.vandermonde_lambda_lower_bound
theorem sz_tcritLower : Formalism.FourierDecayAlt.Sz.TcritLower := Formalism.FourierDecayAlt.P.critical_threshold_lower_bound
theorem wd_dualityList : Formalism.FourierDecayAlt.Wd.DualityList := Formalism.FourierDecayAlt.P.duality_list_holds
theorem wd_kapFormula : Formalism.FourierDecayAlt.Wd.KapFormula := Formalism.FourierDecayAlt.P.kappa_formula_holds
theorem wd_wordFree : Formalism.FourierDecayAlt.Wd.WordFree := Formalism.FourierDecayAlt.P.word_free_of_unused_positions
theorem wd_wordModule : Formalism.FourierDecayAlt.Wd.WordModule := Formalism.FourierDecayAlt.P.word_module_structure
theorem wd_tTFactor : Formalism.FourierDecayAlt.Wd.TTFactor := Formalism.FourierDecayAlt.P.transfer_matrix_factorization
theorem sz_aZeroBound : Formalism.FourierDecayAlt.Sz.AZeroBound := Formalism.FourierDecayAlt.P.a_zero_le_one_sixty
theorem sz_betaOnCut : Formalism.FourierDecayAlt.Sz.BetaOnCut := Formalism.FourierDecayAlt.P.beta_bound_on_boundary
theorem wd_wordsAssemble : Formalism.FourierDecayAlt.Wd.WordsAssemble := Formalism.FourierDecayAlt.P.words_assemble_holds
theorem wd_wordsAll : Formalism.FourierDecayAlt.Wd.WordsAll := Formalism.FourierDecayAlt.P.word_statements_all_hold
theorem fr_lShift : Formalism.FourierDecayAlt.Fr.LShift := Formalism.FourierDecayAlt.P.l_shift_from_determinant
theorem fr_quasiDetT : Formalism.FourierDecayAlt.Fr.QuasiDetT := Formalism.FourierDecayAlt.P.quasi_determinant_from_entries
theorem fr_gaussMinus : Formalism.FourierDecayAlt.Fr.GaussMinus := Formalism.FourierDecayAlt.P.gauss_decomp_minus_letter
theorem fr_rTTEntries : Formalism.FourierDecayAlt.Fr.RTTEntries := Formalism.FourierDecayAlt.P.rtt_relation_entries
theorem fr_adjL : Formalism.FourierDecayAlt.Fr.AdjL := Formalism.FourierDecayAlt.P.adjoint_l_shift_relation
theorem fr_etaLevel : Formalism.FourierDecayAlt.Fr.EtaLevel := Formalism.FourierDecayAlt.P.divided_difference_l
theorem fr_frameModHyp : Formalism.FourierDecayAlt.Fr.FrameModHyp := Formalism.FourierDecayAlt.P.frame_gives_one_letter_hyps
theorem fr_startFrame : Formalism.FourierDecayAlt.Fr.StartFrame := Formalism.FourierDecayAlt.P.start_is_frame
theorem fr_wordJoint : Formalism.FourierDecayAlt.Fr.WordJoint := Formalism.FourierDecayAlt.P.frame_module_of_word
theorem fr_residueStep : Formalism.FourierDecayAlt.Fr.ResidueStep := Formalism.FourierDecayAlt.P.residue_partial_fractions
theorem fr_frameAssemble : Formalism.FourierDecayAlt.Fr.FrameAssemble := Formalism.FourierDecayAlt.P.frame_of_steps
theorem fr_cDiag : Formalism.FourierDecayAlt.Fr.CDiag := Formalism.FourierDecayAlt.P.c_diagonal
theorem fr_cPos : Formalism.FourierDecayAlt.Fr.CPos := Formalism.FourierDecayAlt.P.cPos_true
theorem fr_qPositiveShift : Formalism.FourierDecayAlt.Fr.QPositiveShift := Formalism.FourierDecayAlt.P.q_positive_shift
theorem fr_cPosCut : Formalism.FourierDecayAlt.Fr.CPosCut := Formalism.FourierDecayAlt.P.c_pos_truncated
theorem fr_cPosBase : Formalism.FourierDecayAlt.Fr.CPosBase := Formalism.FourierDecayAlt.P.c_pos_base
theorem admissible_recursion_of_adm : Formalism.FourierDecayAlt.Fr.AdmRecOfAdm := Formalism.FourierDecayAlt.P.admissible_rec_of_admissible
theorem admissible_recursion_of_base : Formalism.FourierDecayAlt.Fr.AdmRecOfBase := Formalism.FourierDecayAlt.P.admissible_rec_of_base_case
theorem fr_frameRecAssemble : Formalism.FourierDecayAlt.Fr.FrameRecAssemble := Formalism.FourierDecayAlt.P.frame_rec_of_steps
theorem fr_cPosCutBase : Formalism.FourierDecayAlt.Fr.CPosCutBase := Formalism.FourierDecayAlt.P.c_pos_truncated_base
theorem position_block_plus : Formalism.FourierDecayAlt.Fr.CoordinateBlockCondition := Formalism.FourierDecayAlt.P.position_block_plus_alt
theorem position_block_difference_minus : Formalism.FourierDecayAlt.Fr.TransposedCoordinateBlockCondition := Formalism.FourierDecayAlt.P.position_block_minus
theorem fr_frameFree : Formalism.FourierDecayAlt.Fr.FrameFree := Formalism.FourierDecayAlt.P.frame_free_of_new_position
theorem g_splitXY : Formalism.FourierDecayAlt.G.SplitXY := Formalism.FourierDecayAlt.P.split_xy_coordinates
theorem g_splitXYMatrix : Formalism.FourierDecayAlt.G.SplitXYMatrix := Formalism.FourierDecayAlt.P.split_xy_matrix
theorem g_limitCoords : Formalism.FourierDecayAlt.G.LimitCoords := Formalism.FourierDecayAlt.P.limit_coordinates
theorem fr_plusAssemble : Formalism.FourierDecayAlt.Fr.PlusAssemble := Formalism.FourierDecayAlt.P.plus_letter_frame_of_data
theorem fr_minusAssemble : Formalism.FourierDecayAlt.Fr.MinusAssemble := Formalism.FourierDecayAlt.P.minus_letter_frame_of_data
theorem fr_residueForm : Formalism.FourierDecayAlt.Fr.ResidueForm := Formalism.FourierDecayAlt.P.fr_residue_form
theorem fr_gaussFormMinus : Formalism.FourierDecayAlt.Fr.GaussFormMinus := Formalism.FourierDecayAlt.P.gauss_form_minus_letter
theorem fr_minusForm : Formalism.FourierDecayAlt.Fr.MinusForm := Formalism.FourierDecayAlt.P.minus_letter_form
theorem fr_zetaConj : Formalism.FourierDecayAlt.Fr.ZetaConj := Formalism.FourierDecayAlt.P.zeta_conj_nabla
theorem fr_eeConj : Formalism.FourierDecayAlt.Fr.EeConj := Formalism.FourierDecayAlt.P.ee_conjugation
theorem fr_frameM : Formalism.FourierDecayAlt.Fr.FrameM := Formalism.FourierDecayAlt.P.frame_adjoint_m
theorem fr_newLetterPlus : Formalism.FourierDecayAlt.Fr.NewLetterPlus := Formalism.FourierDecayAlt.P.new_vector_letter_plus
theorem fr_startEe : Formalism.FourierDecayAlt.Fr.StartEe := Formalism.FourierDecayAlt.P.start_ee
theorem fr_minusLast : Formalism.FourierDecayAlt.Fr.MinusLast := Formalism.FourierDecayAlt.P.minus_letter_last_entry
theorem fr_gaussFormPlus : Formalism.FourierDecayAlt.Fr.GaussFormPlus := Formalism.FourierDecayAlt.P.gauss_form_plus_letter
theorem fr_plusForm : Formalism.FourierDecayAlt.Fr.PlusForm := Formalism.FourierDecayAlt.P.plus_letter_form
theorem g_detMXY : Formalism.FourierDecayAlt.G.DetMXY := Formalism.FourierDecayAlt.P.det_matrix_xy
theorem g_redIntegrable : Formalism.FourierDecayAlt.G.RedIntegrable := Formalism.FourierDecayAlt.P.reduced_integrand_integrable
theorem g_innerXYOfReduced : Formalism.FourierDecayAlt.G.InnerXYOfReduced := Formalism.FourierDecayAlt.P.inner_xy_of_reduced
theorem g_quotientMeasureLong : Formalism.FourierDecayAlt.G.QuotientMeasureLong := Formalism.FourierDecayAlt.P.quotient_measure_long_orbit
theorem g_stabInvariant : Formalism.FourierDecayAlt.G.StabInvariant := Formalism.FourierDecayAlt.P.stabilizer_invariant
theorem g_cofLowerR : Formalism.FourierDecayAlt.G.CofLowerR := Formalism.FourierDecayAlt.P.cofactor_lower_bound_radius
theorem g_chi0Spec : Formalism.FourierDecayAlt.G.Chi0Spec := Formalism.FourierDecayAlt.P.smooth_cutoff_spec
theorem g_ampEq : Formalism.FourierDecayAlt.G.AmpEq := Formalism.FourierDecayAlt.P.amplitude_eq
theorem g_limitCoordsXY : Formalism.FourierDecayAlt.G.LimitCoordsXY := Formalism.FourierDecayAlt.P.limit_coordinates_xy
theorem g_cutMSpec : Formalism.FourierDecayAlt.G.CutMSpec := Formalism.FourierDecayAlt.P.matrix_cutoff_spec
theorem g_critCutSpec : Formalism.FourierDecayAlt.G.CritCutSpec := Formalism.FourierDecayAlt.P.critical_cutoff_spec
theorem g_cutPhiBound : Formalism.FourierDecayAlt.G.CutPhiBound := Formalism.FourierDecayAlt.P.cutoff_phase_bound
theorem g_smallDeltaExists : Formalism.FourierDecayAlt.G.SmallDeltaExists := Formalism.FourierDecayAlt.P.exists_small_delta
theorem g_prodLower : Formalism.FourierDecayAlt.G.ProdLower := Formalism.FourierDecayAlt.P.product_lower_bound
theorem g_tailBound : Formalism.FourierDecayAlt.G.TailBound := Formalism.FourierDecayAlt.P.tailBound_statement
theorem g_tailStepOfBound : Formalism.FourierDecayAlt.G.TailStepOfBound := Formalism.FourierDecayAlt.P.tail_estimate_of_bound
theorem g_germLargeT : Formalism.FourierDecayAlt.G.GermLargeT := Formalism.FourierDecayAlt.P.germ_large_parameter
theorem g_g0RelDeriv : Formalism.FourierDecayAlt.G.PhaseFunctionRelativeDeriv := Formalism.FourierDecayAlt.P.phase_relative_deriv
theorem g_g0NearCrit : Formalism.FourierDecayAlt.G.PhaseFunctionNearCritical := Formalism.FourierDecayAlt.P.phase_near_critical
theorem g_majorantY : Formalism.FourierDecayAlt.G.MajorantY := Formalism.FourierDecayAlt.P.majorant_y
theorem g_ampCritContinuous : Formalism.FourierDecayAlt.G.AmpCritContinuous := Formalism.FourierDecayAlt.P.amplitude_continuous_at_critical
theorem fr_minusTau : Formalism.FourierDecayAlt.Fr.MinusTau := Formalism.FourierDecayAlt.P.minus_letter_tau
theorem fr_minusL : Formalism.FourierDecayAlt.Fr.MinusL := Formalism.FourierDecayAlt.P.minus_letter_l
theorem g_nonStatStepOfParts : Formalism.FourierDecayAlt.G.NonStatStepOfParts := Formalism.FourierDecayAlt.P.nonstationary_estimate_of_parts
theorem g_statStepOfParts : Formalism.FourierDecayAlt.G.StatStepOfParts := Formalism.FourierDecayAlt.P.stationary_estimate_of_parts
theorem g_germRateOfSteps : Formalism.FourierDecayAlt.G.GermRateOfSteps := Formalism.FourierDecayAlt.P.germ_rate_of_estimates
theorem g_wirtingerIBP : Formalism.FourierDecayAlt.G.WirtingerIBP := Formalism.FourierDecayAlt.P.wirtinger_integration_by_parts
theorem g_nonStatPhase : Formalism.FourierDecayAlt.G.NonStatPhase := Formalism.FourierDecayAlt.P.nonstationary_phase
theorem fr_plusTau : Formalism.FourierDecayAlt.Fr.PlusTau := Formalism.FourierDecayAlt.P.plus_letter_tau
theorem fr_plusL : Formalism.FourierDecayAlt.Fr.PlusL := Formalism.FourierDecayAlt.P.plus_letter_l
theorem fr_plusStep : Formalism.FourierDecayAlt.Fr.PlusStep := Formalism.FourierDecayAlt.P.plus_letter_maps_frames
theorem fr_minusStep : Formalism.FourierDecayAlt.Fr.MinusStep := Formalism.FourierDecayAlt.P.minus_letter_maps_frames
theorem fr_frameAll : Formalism.FourierDecayAlt.Fr.FrameAll := Formalism.FourierDecayAlt.P.frame_of_admissible_word
theorem fr_frameWord : Formalism.FourierDecayAlt.Fr.FrameWord := Formalism.FourierDecayAlt.P.frame_eq_word_module
theorem fr_frameAllRec : Formalism.FourierDecayAlt.Fr.FrameAllRec := Formalism.FourierDecayAlt.P.frame_of_recursive_word
theorem g_stationaryPhase : Formalism.FourierDecayAlt.G.StationaryPhase := Formalism.FourierDecayAlt.P.stationary_phase_holomorphic
theorem g_ampBoundFar : Formalism.FourierDecayAlt.G.AmpBoundFar := Formalism.FourierDecayAlt.P.amplitude_bound_far
theorem g_ampBoundCrit : Formalism.FourierDecayAlt.G.AmpBoundCrit := Formalism.FourierDecayAlt.P.amplitude_bound_critical
theorem g_ampLimit : Formalism.FourierDecayAlt.G.AmpLimit := Formalism.FourierDecayAlt.P.amplitude_limit
theorem lemma_b_norm_of_parts : Formalism.FourierDecayAlt.B2.LemmaBNormFromParts := Formalism.FourierDecayAlt.P.lemma_b_normalised_of_parts
theorem lemma_b_from_norm_bound : Formalism.FourierDecayAlt.B2.LemmaBAnyFromNorm := Formalism.FourierDecayAlt.P.lemma_b_any_measure_from_normalised
theorem lemma_b_crude_from_parts : Formalism.FourierDecayAlt.B2.LemmaBCrudeFromParts := Formalism.FourierDecayAlt.P.lemma_b_crude_of_parts
theorem lemma_b_double_of_parts : Formalism.FourierDecayAlt.B2.LemmaBDoubleFromParts := Formalism.FourierDecayAlt.P.doubleB_of_components_true
theorem lemma_b_from_xi_parts : Formalism.FourierDecayAlt.B2.LemmaBFromXiFromParts := Formalism.FourierDecayAlt.P.lemma_b_from_xi_of_parts
theorem haar_measure_unique : Formalism.FourierDecayAlt.B2.HaarUnique := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar
theorem haar_measure_inversion_invariant : Formalism.FourierDecayAlt.B2.HaarInv := Formalism.FourierDecayAlt.P.haar_measure_inversion
theorem haar_invariance_of_unique : Formalism.FourierDecayAlt.B2.HaarInvFromUnique := Formalism.FourierDecayAlt.P.haar_inversion_of_uniqueness
theorem conjugation_haar : Formalism.FourierDecayAlt.B2.ConjHaar := Formalism.FourierDecayAlt.P.conjugation_preserves_haar
theorem compact_conjugation : Formalism.FourierDecayAlt.B2.CompactConj := Formalism.FourierDecayAlt.P.compact_subgroup_conjugation
theorem compact_conjugation_of_unique : Formalism.FourierDecayAlt.B2.CompactConjFromUnique := Formalism.FourierDecayAlt.P.compact_conjugation_of_uniqueness
theorem unipotent_radical_decomposition : Formalism.FourierDecayAlt.B2.NDecomp := Formalism.FourierDecayAlt.P.unipotent_heisenberg_decomposition
theorem unipotent_recursive_haar_measure : Formalism.FourierDecayAlt.B2.NRecHaar := Formalism.FourierDecayAlt.P.unipotent_haar_recursion
theorem unipotent_base_case : Formalism.FourierDecayAlt.B2.NBase := Formalism.FourierDecayAlt.P.unipotent_haar_base_case
theorem heisenberg_haar_exists : Formalism.FourierDecayAlt.B2.HaarNExists := Formalism.FourierDecayAlt.P.unipotent_haar_exists
theorem n_recursion_assembly : Formalism.FourierDecayAlt.B2.AssembleNRec := Formalism.FourierDecayAlt.P.unipotent_recursion_of_parts
theorem haar_measure_unipotent_formula : Formalism.FourierDecayAlt.B2.AssembleHaarN := Formalism.FourierDecayAlt.P.unipotent_haar_of_parts
theorem dilation_heisenberg_action : Formalism.FourierDecayAlt.B2.DilHeis := Formalism.FourierDecayAlt.P.dilation_conjugates_heisenberg
theorem dilation_levi_action : Formalism.FourierDecayAlt.B2.DilLev := Formalism.FourierDecayAlt.P.dilation_levi_conjugation
theorem dilation_heisenberg_measure_preserving : Formalism.FourierDecayAlt.B2.DilHeisMeas := Formalism.FourierDecayAlt.P.dilation_scales_heisenberg_measure
theorem modular_character_recursion : Formalism.FourierDecayAlt.B2.KapRec := Formalism.FourierDecayAlt.P.modular_exponent_recursion
theorem dilation_jacobian_formula : Formalism.FourierDecayAlt.B2.DilJacRaw := Formalism.FourierDecayAlt.P.dilation_jacobian_unipotent
theorem dilation_jacobian_all : Formalism.FourierDecayAlt.B2.DilJacAll := Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting
theorem semidirect_haar : Formalism.FourierDecayAlt.B2.SemiHaar := Formalism.FourierDecayAlt.P.semidirect_product_haar
theorem levi_haar_measure : Formalism.FourierDecayAlt.B2.LevHaar := Formalism.FourierDecayAlt.P.levi_haar_measure_exists
theorem compact_group_haar_measure_exists : Formalism.FourierDecayAlt.B2.CompactHaarExists := Formalism.FourierDecayAlt.P.compact_group_haar_exists
theorem shell_integral : Formalism.FourierDecayAlt.B2.ShellInt := Formalism.FourierDecayAlt.P.spherical_shell_integral
theorem closed_subgroup_general_linear : Formalism.FourierDecayAlt.B2.ClosedG := Formalism.FourierDecayAlt.P.unitary_group_closed
theorem closed_subgroup_unipotent_radical : Formalism.FourierDecayAlt.B2.ClosedN := Formalism.FourierDecayAlt.P.unipotent_radical_closed
theorem heisenberg_multiplication : Formalism.FourierDecayAlt.B2.HeisMul := Formalism.FourierDecayAlt.P.heisMul_statement
theorem heisenberg_group_inverse : Formalism.FourierDecayAlt.B2.HeisInv := Formalism.FourierDecayAlt.P.heisenberg_inverse
theorem heisenberg_group_closed : Formalism.FourierDecayAlt.B2.HeisClosed := Formalism.FourierDecayAlt.P.heisenberg_subgroup_closed
theorem heisenberg_haar : Formalism.FourierDecayAlt.B2.HeisHaar := Formalism.FourierDecayAlt.P.heisenberg_haar_measure
theorem heisenberg_conjugation_levi : Formalism.FourierDecayAlt.B2.HeisConjLev := Formalism.FourierDecayAlt.P.heisenberg_conjugation_by_levi
theorem heisenberg_conjugation_measure_preserving : Formalism.FourierDecayAlt.B2.HeisConjLevMeas := Formalism.FourierDecayAlt.P.heisenberg_levi_conjugation_measure
theorem crude_integral_of_volume : Formalism.FourierDecayAlt.B2.GNIntCrudeFromVol := Formalism.FourierDecayAlt.P.norm_power_integrable_crude_of_volume
theorem cc_from_g_n : Formalism.FourierDecayAlt.B2.CCFromGN := Formalism.FourierDecayAlt.P.matrix_coefficient_bound_by_norm
theorem crude_cc_integral_all : Formalism.FourierDecayAlt.B2.CCIntCrudeAll := Formalism.FourierDecayAlt.P.matrix_coefficient_integrable_crude_all
theorem cc_integral_double : Formalism.FourierDecayAlt.B2.CCIntDouble := Formalism.FourierDecayAlt.P.matrix_coefficient_integrable_double
theorem integral_cc_assembly : Formalism.FourierDecayAlt.B2.AssembleCCInt := Formalism.FourierDecayAlt.P.matrix_coefficient_integrable_of_parts
theorem volume_sharp_of_exact : Formalism.FourierDecayAlt.B2.VolSharpFromExact := Formalism.FourierDecayAlt.P.sharp_volume_of_exact
theorem crude_volume_bound : Formalism.FourierDecayAlt.B2.VolCrude := Formalism.FourierDecayAlt.P.norm_ball_volume_crude
theorem g_from_diagonal : Formalism.FourierDecayAlt.B2.GFromDiag := Formalism.FourierDecayAlt.P.group_measure_from_diagonal
theorem g_n_integral_crude : Formalism.FourierDecayAlt.B2.GNIntCrude := Formalism.FourierDecayAlt.P.norm_power_integrable_crude
theorem g_n_sharp_of_volume : Formalism.FourierDecayAlt.B2.GNIntSharpFromVol := Formalism.FourierDecayAlt.P.norm_power_integrable_sharp_of_volume
theorem haar_w_of_compact : Formalism.FourierDecayAlt.B2.HaarWFromCompact := Formalism.FourierDecayAlt.P.weyl_haar_from_compact
theorem conjugation_invariance_raw : Formalism.FourierDecayAlt.B2.ConjInvRaw := Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof
theorem conjugation_invariance_all : Formalism.FourierDecayAlt.B2.ConjInvAll := Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting
theorem conjugation_invariance_assembly : Formalism.FourierDecayAlt.B2.AssembleConjInv := Formalism.FourierDecayAlt.P.conjugation_invariance_of_parts
theorem heisenberg_action : Formalism.FourierDecayAlt.B2.HeisAct := Formalism.FourierDecayAlt.P.heisenberg_action_formula
theorem heisenberg_membership : Formalism.FourierDecayAlt.B2.HeisMem := Formalism.FourierDecayAlt.P.heisenberg_mem_unipotent
theorem crude_integral_assembly : Formalism.FourierDecayAlt.B2.AssembleCCIntCrude := Formalism.FourierDecayAlt.P.crude_integrability_of_parts
theorem z_exists : Formalism.FourierDecayAlt.B2.ZExists := Formalism.FourierDecayAlt.P.base_vector_exists
theorem chiExists_true : Formalism.FourierDecayAlt.B2.ChiExists := Formalism.FourierDecayAlt.P.character_exists_alt
theorem existence_assembly : Formalism.FourierDecayAlt.B2.AssembleExists := Formalism.FourierDecayAlt.P.setting_exists_of_parts
theorem meanSplit_gauss_true : Formalism.FourierDecayAlt.A6.MeanSplit := Formalism.FourierDecayAlt.P.doubleMeanSplit
theorem p_orthogonality : Formalism.FourierDecayAlt.A6.POrth := Formalism.FourierDecayAlt.P.partialMeansOrthogonal
theorem orthogonal_projection_norm_bound : Formalism.FourierDecayAlt.A6.OrthNorm := Formalism.FourierDecayAlt.P.orthogonalMeanNorm
theorem average_bound : Formalism.FourierDecayAlt.A6.AvgBound := Formalism.FourierDecayAlt.P.averageBound
theorem average_bound_from_local_pieces : Formalism.FourierDecayAlt.A6.AvgBoundAssemble := Formalism.FourierDecayAlt.P.averageBoundOfSteps
theorem dilation_jacobian_assembly : Formalism.FourierDecayAlt.B2.AssembleDilJac := Formalism.FourierDecayAlt.P.dilation_jacobian_of_parts
theorem single_move_membership : Formalism.FourierDecayAlt.B2.OneStepMem := Formalism.FourierDecayAlt.P.stabilizer_one_parameter_mem
theorem single_move_coordinates : Formalism.FourierDecayAlt.B2.OneStepCoord := Formalism.FourierDecayAlt.P.rank_one_coordinates_formula
theorem cone_invariant : Formalism.FourierDecayAlt.B2.ConeInv := Formalism.FourierDecayAlt.P.isotropic_cone_invariance
theorem coneFinite_true : Formalism.FourierDecayAlt.B2.ConeFinite := Formalism.FourierDecayAlt.P.isotropic_cone_finite_measure
theorem stabilizer_decomposition : Formalism.FourierDecayAlt.B2.StabDecomp := Formalism.FourierDecayAlt.P.stabilizer_factorization
theorem local_germ_expansion : Formalism.FourierDecayAlt.A6.GermAssemble := Formalism.FourierDecayAlt.P.germExpansionOfSteps
theorem g_tailStep : Formalism.FourierDecayAlt.G.TailStep := Formalism.FourierDecayAlt.P.orbit_tail_estimate
theorem g_innerXY : Formalism.FourierDecayAlt.G.InnerXY := Formalism.FourierDecayAlt.P.change_of_variables_xy
theorem g_nonStatStep : Formalism.FourierDecayAlt.G.NonStatStep := Formalism.FourierDecayAlt.P.nonstationary_estimate
theorem g_statStep : Formalism.FourierDecayAlt.G.StatStep := Formalism.FourierDecayAlt.P.stationary_estimate
theorem g_germRate : Formalism.FourierDecayAlt.G.GermRate := Formalism.FourierDecayAlt.P.germ_rate
theorem g_germ : Formalism.FourierDecayAlt.G.Germ := Formalism.FourierDecayAlt.P.germExpansion_true
theorem germ_kernel_expansion_from_pieces : Formalism.FourierDecayAlt.A6.GermKernelAssemble := Formalism.FourierDecayAlt.P.germExpansionKernelOfSteps
theorem tc_domMinOfText : Formalism.FourierDecayAlt.TC.DomMinOfText := Formalism.FourierDecayAlt.P.domination_minimum_of_text
theorem tc_afterOfOld : Formalism.FourierDecayAlt.TC.AfterOfOld := Formalism.FourierDecayAlt.P.after_of_old
theorem tc_majorantPSD : Formalism.FourierDecayAlt.TC.MajorantPSD := Formalism.FourierDecayAlt.P.majorant_positive_semidefinite
theorem tc_domMonoE : Formalism.FourierDecayAlt.TC.DomMonoE := Formalism.FourierDecayAlt.P.domination_monotone
theorem tc_oneLevelAfter : Formalism.FourierDecayAlt.TC.OneLevelAfter := Formalism.FourierDecayAlt.P.one_level_after
theorem tc_oneLevelAfterOfOld : Formalism.FourierDecayAlt.TC.OneLevelAfterOfOld := Formalism.FourierDecayAlt.P.one_level_after_of_old
theorem tc_theoremAAfter : Formalism.FourierDecayAlt.TC.TheoremAAfter := Formalism.FourierDecayAlt.P.theorem_a_after
theorem tc_theoremAAfterOfSteps : Formalism.FourierDecayAlt.TC.TheoremAAfterOfSteps := Formalism.FourierDecayAlt.P.theorem_a_after_of_parts
theorem tc_theoremAOfAfter : Formalism.FourierDecayAlt.TC.TheoremAOfAfter := Formalism.FourierDecayAlt.P.theorem_a_of_after
theorem tc_domMinOfTextA : Formalism.FourierDecayAlt.TC.DomMinOfTextA := Formalism.FourierDecayAlt.P.domMinOfTextA_statement
theorem tc_afterOfOldA : Formalism.FourierDecayAlt.TC.AfterOfOldA := Formalism.FourierDecayAlt.P.afterOfOldA_statement
theorem tc_majorantPSDA : Formalism.FourierDecayAlt.TC.MajorantPSDA := Formalism.FourierDecayAlt.P.majorantPSDA_statement
theorem tc_oneLevelAfterA : Formalism.FourierDecayAlt.TC.OneLevelAfterA := Formalism.FourierDecayAlt.P.oneLevelAfterA_statement
theorem tc_oneLevelAfterOfOldA : Formalism.FourierDecayAlt.TC.OneLevelAfterOfOldA := Formalism.FourierDecayAlt.P.oneLevelAfterOfOldA_statement
theorem tc_reductionAfter : Formalism.FourierDecayAlt.TC.ReductionAfter := Formalism.FourierDecayAlt.P.reduction_after
theorem tc_reductionAfterOfSteps : Formalism.FourierDecayAlt.TC.ReductionAfterOfSteps := Formalism.FourierDecayAlt.P.reduction_after_of_parts
theorem tc_reductionOfAfter : Formalism.FourierDecayAlt.TC.ReductionOfAfter := Formalism.FourierDecayAlt.P.reduction_of_after_inequality
theorem tc_domAgree : Formalism.FourierDecayAlt.TC.DomAgree := Formalism.FourierDecayAlt.P.domination_agree
theorem tc_domTextOfSystems : Formalism.FourierDecayAlt.TC.DomTextOfSystems := Formalism.FourierDecayAlt.P.domination_text_of_systems
theorem tc_recHypAfterOfOld : Formalism.FourierDecayAlt.TC.RecHypAfterOfOld := Formalism.FourierDecayAlt.P.recursion_hypothesis_after_of_old
theorem recursion_gives_densityData_after' : Formalism.FourierDecayAlt.TC.RecursionGivesUniformBoundsAfter := Formalism.FourierDecayAlt.P.recursion_gives_explicit_after
theorem tc_eOfDens : Formalism.FourierDecayAlt.TC.EOfDens := Formalism.FourierDecayAlt.P.exponent_of_densities
theorem tc_productOfEMax : Formalism.FourierDecayAlt.TC.ProductOfEMax := Formalism.FourierDecayAlt.P.product_of_exponent_max
theorem tc_densLeTwo : Formalism.FourierDecayAlt.TC.DensLeTwo := Formalism.FourierDecayAlt.P.density_le_two
theorem tc_densSize : Formalism.FourierDecayAlt.TC.DensSize := Formalism.FourierDecayAlt.P.density_size
theorem tc_sumBoundMax : Formalism.FourierDecayAlt.TC.SumBoundMax := Formalism.FourierDecayAlt.P.sum_bound_max
theorem tc_recursionWithDens : Formalism.FourierDecayAlt.TC.RecursionWithDens := Formalism.FourierDecayAlt.P.recursion_with_densities
theorem tc_onceOnlyMax : Formalism.FourierDecayAlt.TC.OnceOnlyMax := Formalism.FourierDecayAlt.P.once_only_max
theorem densityData_covers' : Formalism.FourierDecayAlt.TC.MassDataCovers := Formalism.FourierDecayAlt.P.massData_covers
theorem germ_phi_assembly : Formalism.FourierDecayAlt.A6.GermPhiAssemble := Formalism.FourierDecayAlt.P.germExpansionOfTestFunction
theorem closed_subgroup_weyl : Formalism.FourierDecayAlt.B2.ClosedW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed
theorem closed_subgroup_opposite_weyl : Formalism.FourierDecayAlt.B2.ClosedWb := Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed
theorem compact_w : Formalism.FourierDecayAlt.B2.CompactW := Formalism.FourierDecayAlt.P.weyl_subgroup_compact
theorem haar_measure_general_linear_exists : Formalism.FourierDecayAlt.B2.HaarGExists := Formalism.FourierDecayAlt.P.unitary_group_haar_exists
theorem haar_wb_exists : Formalism.FourierDecayAlt.B2.HaarWbExists := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists
theorem haar_measure_on_weyl_subgroup_exists : Formalism.FourierDecayAlt.B2.HaarWExists := Formalism.FourierDecayAlt.P.weyl_haar_exists
theorem theta_omega_assembly : Formalism.FourierDecayAlt.A6.ThOmAssemble := Formalism.FourierDecayAlt.P.thetaOnDomainOfSteps
theorem thetaExistence_recursion_of_components : Formalism.FourierDecayAlt.A6.ThetaExistenceInductive := Formalism.FourierDecayAlt.P.thetaExistsStepOfSteps
theorem u_norm_bound : Formalism.FourierDecayAlt.A6.UNormBound := Formalism.FourierDecayAlt.P.averaged_vector_norm_bound
theorem positive_semidefinite_restriction : Formalism.FourierDecayAlt.A6.CutPSD := Formalism.FourierDecayAlt.P.cut_posSemidef
theorem unipotent_block : Formalism.FourierDecayAlt.A6.UBlock := Formalism.FourierDecayAlt.P.heads_distinct_determinant_orthogonal
theorem average_data_exists : Formalism.FourierDecayAlt.A6.AvgDataExists := Formalism.FourierDecayAlt.P.averaged_vector_choices_exist
theorem norm_evaluation : Formalism.FourierDecayAlt.A6.CutNormEval := Formalism.FourierDecayAlt.P.truncated_average_norm_formula
theorem lattice_finite : Formalism.FourierDecayAlt.A6.LatFinite := Formalism.FourierDecayAlt.P.lattice_family_finite
theorem integral_lattice_refinement : Formalism.FourierDecayAlt.A6.IntLatRefine := Formalism.FourierDecayAlt.P.integral_lattice_refinement_identity
theorem integral_k_refine : Formalism.FourierDecayAlt.A6.IntKRefine := Formalism.FourierDecayAlt.P.integral_field_refinement
theorem volume_scaling_formula : Formalism.FourierDecayAlt.A6.VolScale := Formalism.FourierDecayAlt.P.volume_scaling_identity
theorem orthogonal_complement_lattice : Formalism.FourierDecayAlt.A6.PerpLat := Formalism.FourierDecayAlt.P.orthogonal_lattice_properties
theorem stationary_phase_formula : Formalism.FourierDecayAlt.A6.StationaryAssemble := Formalism.FourierDecayAlt.P.stationaryPhaseOfSteps
theorem theta_series_lower_bound : Formalism.FourierDecayAlt.A6.ThxLower := Formalism.FourierDecayAlt.P.thetaAverageLower
theorem character_mean : Formalism.FourierDecayAlt.A6.CharMean := Formalism.FourierDecayAlt.P.characterMean
theorem perpendicular_dual : Formalism.FourierDecayAlt.A6.PerpDual := Formalism.FourierDecayAlt.P.annihilatorCharacters
theorem lattice_choice_exists : Formalism.FourierDecayAlt.A6.LatChoice := Formalism.FourierDecayAlt.P.compactOpenChoice
theorem modulus_locally_constant : Formalism.FourierDecayAlt.A6.ModLocConst := Formalism.FourierDecayAlt.P.modulusLocallyConstant
theorem small_units : Formalism.FourierDecayAlt.A6.SmallUnits := Formalism.FourierDecayAlt.P.smallUnits
theorem tc_domScaleTop : Formalism.FourierDecayAlt.TC.DomScaleTop := Formalism.FourierDecayAlt.P.domination_scale_top
theorem tc_recHypScaleTop : Formalism.FourierDecayAlt.TC.RecHypScaleTop := Formalism.FourierDecayAlt.P.recursion_hypothesis_scale_top
theorem tc_domAfterOfLocal : Formalism.FourierDecayAlt.TC.DomAfterOfLocal := Formalism.FourierDecayAlt.P.domination_after_of_local
theorem tc_densSum : Formalism.FourierDecayAlt.TC.DensSum := Formalism.FourierDecayAlt.P.density_sum
theorem tc_densChain : Formalism.FourierDecayAlt.TC.DensChain := Formalism.FourierDecayAlt.P.density_chain
theorem small_modules_classification : Formalism.FourierDecayAlt.A6.SmallModules := Formalism.FourierDecayAlt.P.smallModules
theorem rootsFinite_true : Formalism.FourierDecayAlt.A6.RootsFinite := Formalism.FourierDecayAlt.P.rootsFinite
theorem roots_separated_in_residue_field : Formalism.FourierDecayAlt.A6.RootsSeparated := Formalism.FourierDecayAlt.P.rootsSeparated
theorem exhaust_true : Formalism.FourierDecayAlt.A6.Exhaust := Formalism.FourierDecayAlt.P.rootStableExhaustion
theorem parametrisation : Formalism.FourierDecayAlt.A6.Param := Formalism.FourierDecayAlt.P.blockParametrisation
theorem kp_hermitian : Formalism.FourierDecayAlt.A6.KpHerm := Formalism.FourierDecayAlt.P.gramKernelHermitian
theorem shift_unit : Formalism.FourierDecayAlt.A6.ShiftUnit := Formalism.FourierDecayAlt.P.shiftUnit_statement
theorem shiftSmall_true : Formalism.FourierDecayAlt.A6.ShiftSmall := Formalism.FourierDecayAlt.P.shiftSmall_statement
theorem truncation_same_on_ring : Formalism.FourierDecayAlt.A6.CutSame := Formalism.FourierDecayAlt.P.rootCutStable
theorem root_correction_term : Formalism.FourierDecayAlt.A6.RootCorr := Formalism.FourierDecayAlt.P.rootCorrection
theorem theta_series_basic_bounds : Formalism.FourierDecayAlt.A6.ThxBasic := Formalism.FourierDecayAlt.P.averaged_kernel_periodic_psd
theorem theta_x_sum : Formalism.FourierDecayAlt.A6.ThxSum := Formalism.FourierDecayAlt.P.averaged_kernel_parseval
theorem support_module_description : Formalism.FourierDecayAlt.A6.SupportModule := Formalism.FourierDecayAlt.P.finite_family_truncation_module
theorem c_size_one : Formalism.FourierDecayAlt.A6.CSizeOne := Formalism.FourierDecayAlt.P.head_size_one_in_GL
theorem iteration_bound_from_local_pieces : Formalism.FourierDecayAlt.A6.ThetaExistenceInductiveFromPieces := Formalism.FourierDecayAlt.P.induction_from_assembled_pieces
theorem parseval_group : Formalism.FourierDecayAlt.A6.ParsevalGroup := Formalism.FourierDecayAlt.P.parsevalGroup_statement
theorem gram_realisation_truncated : Formalism.FourierDecayAlt.A6.GramRealiseCut := Formalism.FourierDecayAlt.P.gramRealisation
theorem psd_entry_bound : Formalism.FourierDecayAlt.A6.PSDEntryBound := Formalism.FourierDecayAlt.P.posSemidefEntryBound
theorem psd_closed : Formalism.FourierDecayAlt.A6.PSDClosed := Formalism.FourierDecayAlt.P.posSemidefClosed
theorem bounded_subsequence_exists : Formalism.FourierDecayAlt.A6.BoundedSubseq := Formalism.FourierDecayAlt.P.boundedSubsequence
theorem non_stationary_phase : Formalism.FourierDecayAlt.A6.NonStationary := Formalism.FourierDecayAlt.P.nonStationary
theorem stabiliser_haar : Formalism.FourierDecayAlt.B2.StabHaar := Formalism.FourierDecayAlt.P.stabilizer_haar_measure
theorem stabilizer_haar_integral_decomposition : Formalism.FourierDecayAlt.B2.AssembleStab := Formalism.FourierDecayAlt.P.stabilizer_haar_of_parts
theorem single_move_integral : Formalism.FourierDecayAlt.B2.OneStepInt := Formalism.FourierDecayAlt.P.stabilizer_integration_formula
theorem single_move_assembly : Formalism.FourierDecayAlt.B2.AssembleOneStep := Formalism.FourierDecayAlt.P.stabilizer_integration_of_parts
theorem null_direction_vanishing : Formalism.FourierDecayAlt.B2.OneStepNull := Formalism.FourierDecayAlt.P.stabilizer_null_set
theorem null_direction_from_integral : Formalism.FourierDecayAlt.B2.OneStepNullFromInt := Formalism.FourierDecayAlt.P.stabilizer_null_of_integrable
theorem germ_identity_assembly : Formalism.FourierDecayAlt.A6.GermIdentityAssemble := Formalism.FourierDecayAlt.P.germIdentityOfSteps
theorem integral_norm_b_of_norm : Formalism.FourierDecayAlt.B2.IntNormBFromNorm := Formalism.FourierDecayAlt.P.normalisation_every_setting
theorem g_n_lower : Formalism.FourierDecayAlt.B2.GNLower := Formalism.FourierDecayAlt.P.matrix_norm_ge_one
theorem hilbert_schmidt_block_norm_bound : Formalism.FourierDecayAlt.B2.HSBlock := Formalism.FourierDecayAlt.P.hilbert_schmidt_block
theorem volume_exact : Formalism.FourierDecayAlt.B2.VolExact := Formalism.FourierDecayAlt.P.norm_ball_volume_exact
theorem volume_sharp : Formalism.FourierDecayAlt.B2.VolSharp := Formalism.FourierDecayAlt.P.norm_ball_volume_sharp
theorem gaussian_independence : Formalism.FourierDecayAlt.A6.GaussIndep := Formalism.FourierDecayAlt.P.gauss_index_independent_of_choice
theorem gaussian_hessian_formula : Formalism.FourierDecayAlt.A6.GaussHessAssemble := Formalism.FourierDecayAlt.P.gauss_hessian_index_of_parts
theorem admissible_gaussian_small : Formalism.FourierDecayAlt.A6.GaussAdmSmall := Formalism.FourierDecayAlt.P.admissible_gauss_sum_small
theorem oscillatory_invariant : Formalism.FourierDecayAlt.A6.OscInvariant := Formalism.FourierDecayAlt.P.oscillatory_integral_invariant
theorem kernel_from_bilinear : Formalism.FourierDecayAlt.A6.KpFromBB := Formalism.FourierDecayAlt.P.kernel_as_coset_sum
theorem locally_constant_phase : Formalism.FourierDecayAlt.A6.LocConst := Formalism.FourierDecayAlt.P.phase_locally_constant
theorem phase_critical_points_nondegenerate : Formalism.FourierDecayAlt.A6.CritPoints := Formalism.FourierDecayAlt.P.phase_critical_points
theorem critical_value : Formalism.FourierDecayAlt.A6.CritValue := Formalism.FourierDecayAlt.P.phase_critical_value
theorem hessian_jet : Formalism.FourierDecayAlt.A6.HessianJet := Formalism.FourierDecayAlt.P.hessian_jet_formula
theorem hessian_determinant_formula : Formalism.FourierDecayAlt.A6.HessDet := Formalism.FourierDecayAlt.P.phase_hessian_determinant
theorem gaussModulus_true : Formalism.FourierDecayAlt.A6.GaussModulus := Formalism.FourierDecayAlt.P.gauss_sum_modulus_of_lattice
theorem unipotent_weyl_facts : Formalism.FourierDecayAlt.B2.UWbFacts := Formalism.FourierDecayAlt.P.unipotent_weyl_properties
theorem weight_factor : Formalism.FourierDecayAlt.B2.WeightFactor := Formalism.FourierDecayAlt.P.weight_factorization
theorem hyperbolic_inverse_formula : Formalism.FourierDecayAlt.B2.HypInv := Formalism.FourierDecayAlt.P.hyperbolic_element_inverse
theorem rank_one_membership : Formalism.FourierDecayAlt.B2.RankOneMem := Formalism.FourierDecayAlt.P.b2_rank_one_mem
theorem rank_one_coordinates : Formalism.FourierDecayAlt.B2.RankOneCoord := Formalism.FourierDecayAlt.P.b2_rank_one_coord
theorem rank_one_integral_formula : Formalism.FourierDecayAlt.B2.RankOneInt := Formalism.FourierDecayAlt.P.rank_one_integration_formula
theorem head_reduction : Formalism.FourierDecayAlt.A6.HeadReduction := Formalism.FourierDecayAlt.P.head_reduction_lemma
theorem wb_from_diagonal : Formalism.FourierDecayAlt.B2.WbFromDiag := Formalism.FourierDecayAlt.P.weyl_measure_from_diagonal
theorem rank_one_assembly : Formalism.FourierDecayAlt.B2.AssembleRankOne := Formalism.FourierDecayAlt.P.rank_one_formula_of_parts
theorem integral_formula_from_pieces : Formalism.FourierDecayAlt.B2.AssembleInt := Formalism.FourierDecayAlt.P.integration_formula_of_parts
theorem integral_norm_from_constant : Formalism.FourierDecayAlt.B2.IntNormFromConst := Formalism.FourierDecayAlt.P.integral_normalisation_from_constant
theorem padicMorse_true : Formalism.FourierDecayAlt.A6.MorseLemma := Formalism.FourierDecayAlt.P.morseLemma
theorem square_near : Formalism.FourierDecayAlt.A6.SquareNear := Formalism.FourierDecayAlt.P.square_near_unit
theorem phase_difference : Formalism.FourierDecayAlt.A6.PhaseDiff := Formalism.FourierDecayAlt.P.phase_difference_estimate
theorem change_of_variables : Formalism.FourierDecayAlt.A6.ChangeVar := Formalism.FourierDecayAlt.P.padic_change_of_variables
theorem c_size_add_block : Formalism.FourierDecayAlt.A6.CSizeAddBlock := Formalism.FourierDecayAlt.P.head_size_add_block
theorem u_gram_eq : Formalism.FourierDecayAlt.A6.UGramEq := Formalism.FourierDecayAlt.P.gram_equality_of_vectors
theorem jx_pSDAgree : Formalism.FourierDecayAlt.J.PSDAgree := Formalism.FourierDecayAlt.P.psd_agree
theorem jx_pSDTranspose : Formalism.FourierDecayAlt.J.PSDTranspose := Formalism.FourierDecayAlt.P.psd_transpose
theorem jx_axiomsAgree : Formalism.FourierDecayAlt.J.AxiomsAgree := Formalism.FourierDecayAlt.P.axioms_agree
theorem jx_towersAgree : Formalism.FourierDecayAlt.J.TowersAgree := Formalism.FourierDecayAlt.P.towers_agree
theorem jx_formsAgree : Formalism.FourierDecayAlt.J.FormsAgree := Formalism.FourierDecayAlt.P.forms_agree
theorem jx_boxSumLattice : Formalism.FourierDecayAlt.J.BoxSumLattice := Formalism.FourierDecayAlt.P.box_sum_lattice
theorem jx_majIsProf : Formalism.FourierDecayAlt.J.MajIsProf := Formalism.FourierDecayAlt.P.majorant_is_profinite
theorem jx_supAIsCore : Formalism.FourierDecayAlt.J.SupAIsCore := Formalism.FourierDecayAlt.P.supremum_A_is_majorant
theorem jx_thrMono : Formalism.FourierDecayAlt.J.ThresholdsMonotone := Formalism.FourierDecayAlt.P.threshold_mono
theorem jx_instSizes : Formalism.FourierDecayAlt.J.InstSizes := Formalism.FourierDecayAlt.P.instance_sizes
theorem jx_instLatticeSums : Formalism.FourierDecayAlt.J.InstLatticeSums := Formalism.FourierDecayAlt.P.instance_lattice_sums
theorem jx_sizesToRecursion : Formalism.FourierDecayAlt.J.SizesToRecursion := Formalism.FourierDecayAlt.P.sizes_to_recursion
theorem jx_globPositive : Formalism.FourierDecayAlt.J.GlobPositive := Formalism.FourierDecayAlt.P.global_positive
theorem jx_majMono : Formalism.FourierDecayAlt.J.MajMono := Formalism.FourierDecayAlt.P.majorant_mono
theorem jx_latticeSumsJoint : Formalism.FourierDecayAlt.J.LatticeSumsJoint := Formalism.FourierDecayAlt.P.lattice_sums_joint
theorem jx_levelSizesJoint : Formalism.FourierDecayAlt.J.LevelSizesJoint := Formalism.FourierDecayAlt.P.level_sizes_joint
theorem jx_levelSizesJointMean : Formalism.FourierDecayAlt.J.LevelSizesJointMean := Formalism.FourierDecayAlt.P.level_sizes_joint_mean
theorem jx_nuIndex : Formalism.FourierDecayAlt.J.NuIndex := Formalism.FourierDecayAlt.P.nu_index
theorem jx_blockLattices : Formalism.FourierDecayAlt.J.BlockLattices := Formalism.FourierDecayAlt.P.block_lattices
theorem jx_embFacts : Formalism.FourierDecayAlt.J.EmbFacts := Formalism.FourierDecayAlt.P.embedding_facts
theorem jx_euclidFrame : Formalism.FourierDecayAlt.J.EuclidFrame := Formalism.FourierDecayAlt.P.euclidean_frame
theorem crossVanish_true : Formalism.FourierDecayAlt.A6.CrossVanish := Formalism.FourierDecayAlt.P.crossTermsVanish
theorem jx_thresholdBelowOne : Formalism.FourierDecayAlt.J.ThresholdBelowOne := Formalism.FourierDecayAlt.P.threshold_below_one
theorem jx_lettersAtPlaces : Formalism.FourierDecayAlt.J.LettersAtPlaces := Formalism.FourierDecayAlt.P.letters_at_places
theorem jx_waveLetters : Formalism.FourierDecayAlt.J.WaveLetters := Formalism.FourierDecayAlt.P.wave_letters
theorem jx_waveLettersOne : Formalism.FourierDecayAlt.J.WaveLettersOne := Formalism.FourierDecayAlt.P.wave_letters_one
theorem jx_liftLetters : Formalism.FourierDecayAlt.J.LiftLetters := Formalism.FourierDecayAlt.P.lift_letters
theorem jx_waveLettersMix : Formalism.FourierDecayAlt.J.WaveLettersMix := Formalism.FourierDecayAlt.P.wave_letters_mixed
theorem jx_liftLettersMix : Formalism.FourierDecayAlt.J.LiftLettersMix := Formalism.FourierDecayAlt.P.lift_letters_mixed
theorem jx_scaleOk : Formalism.FourierDecayAlt.J.ScaleOk := Formalism.FourierDecayAlt.P.scaling_bound
theorem jx_phaseOk : Formalism.FourierDecayAlt.J.PhaseOk := Formalism.FourierDecayAlt.P.phaseOk_statement
theorem jx_outsideOk : Formalism.FourierDecayAlt.J.OutsideOk := Formalism.FourierDecayAlt.P.outside_bound
theorem jx_outsideSysOk : Formalism.FourierDecayAlt.J.OutsideSysOk := Formalism.FourierDecayAlt.P.outside_systems_bound
theorem jx_outsideDomination : Formalism.FourierDecayAlt.J.OutsideDomination := Formalism.FourierDecayAlt.P.outside_domination
theorem jx_uniformMajorant : Formalism.FourierDecayAlt.J.UniformMajorant := Formalism.FourierDecayAlt.P.uniformMajorant_statement
theorem jx_uniformMajorantOn : Formalism.FourierDecayAlt.J.UniformMajorantOn := Formalism.FourierDecayAlt.P.uniform_majorant_on
theorem jx_tracePairing : Formalism.FourierDecayAlt.J.TracePairing := Formalism.FourierDecayAlt.P.trace_pairing
theorem jx_traceDual : Formalism.FourierDecayAlt.J.TraceDual := Formalism.FourierDecayAlt.P.trace_dual_alt
theorem jx_blockFrame : Formalism.FourierDecayAlt.J.BlockFrame := Formalism.FourierDecayAlt.P.block_frame
theorem jx_dualCovolume : Formalism.FourierDecayAlt.J.DualCovolume := Formalism.FourierDecayAlt.P.dual_covolume
theorem jx_dualMeasureBound : Formalism.FourierDecayAlt.J.DualMeasureBound := Formalism.FourierDecayAlt.P.dual_measure_bound
theorem jx_dualCovolumeCV : Formalism.FourierDecayAlt.J.DualCovolumeCV := Formalism.FourierDecayAlt.P.dual_covolume_change_of_variables
theorem jx_poissonJoint : Formalism.FourierDecayAlt.J.PoissonJoint := Formalism.FourierDecayAlt.P.poisson_joint
theorem jx_localPullback : Formalism.FourierDecayAlt.J.LocalPullback := Formalism.FourierDecayAlt.P.local_pullback
theorem jx_localUnitHeads : Formalism.FourierDecayAlt.J.LocalUnitHeads := Formalism.FourierDecayAlt.P.local_unit_heads
theorem jx_topPullback : Formalism.FourierDecayAlt.J.TopPullback := Formalism.FourierDecayAlt.P.top_pullback
theorem jx_axiomsFromSystems : Formalism.FourierDecayAlt.J.AxiomsFromSystems := Formalism.FourierDecayAlt.P.axioms_from_systems
theorem jx_globalOfLocal : Formalism.FourierDecayAlt.J.GlobalOfLocal := Formalism.FourierDecayAlt.P.global_of_local
theorem jx_axiomsFromFamilies : Formalism.FourierDecayAlt.J.AxiomsFromFamilies := Formalism.FourierDecayAlt.P.axioms_from_families
theorem jx_kernelOfLocal : Formalism.FourierDecayAlt.J.KernelOfLocal := Formalism.FourierDecayAlt.P.kernel_of_local
theorem jx_transformAtZero : Formalism.FourierDecayAlt.J.TransformAtZero := Formalism.FourierDecayAlt.P.fourier_transform_at_zero
theorem jx_poissonStepJoint : Formalism.FourierDecayAlt.J.PoissonStepJoint := Formalism.FourierDecayAlt.P.poisson_level_joint
theorem jx_poissonJointTA : Formalism.FourierDecayAlt.J.PoissonJointTA := Formalism.FourierDecayAlt.P.poisson_joint_first_reduction
theorem jx_poissonAgree : Formalism.FourierDecayAlt.J.PoissonAgree := Formalism.FourierDecayAlt.P.poisson_forms_agree
theorem jx_blockPoissonFrame : Formalism.FourierDecayAlt.J.BlockPoissonFrame := Formalism.FourierDecayAlt.P.block_poisson_frame
theorem jx_xIsLamOne : Formalism.FourierDecayAlt.J.XIsLamOne := Formalism.FourierDecayAlt.P.lattice_x_eq_lambda_one
theorem jx_frameProducts : Formalism.FourierDecayAlt.J.FrameProducts := Formalism.FourierDecayAlt.P.frame_product_identities
theorem jx_mainJoint : Formalism.FourierDecayAlt.J.MainJoint := Formalism.FourierDecayAlt.P.joint_theorem_A
theorem jx_mainJointForm : Formalism.FourierDecayAlt.J.MainJointForm := Formalism.FourierDecayAlt.P.joint_form_theorem_A
theorem jx_mainJointInst : Formalism.FourierDecayAlt.J.MainJointInst := Formalism.FourierDecayAlt.P.joint_instance_theorem_A
theorem jx_schurProduct : Formalism.FourierDecayAlt.J.SchurProduct := Formalism.FourierDecayAlt.P.schur_product
theorem jx_productDomination : Formalism.FourierDecayAlt.J.ProductDomination := Formalism.FourierDecayAlt.P.product_domination
theorem jx_diagScale : Formalism.FourierDecayAlt.J.DiagScale := Formalism.FourierDecayAlt.P.diagonal_scaling
theorem jx_productLemma : Formalism.FourierDecayAlt.J.ProductLemma := Formalism.FourierDecayAlt.P.product_lemma
theorem jx_localKernelPSD : Formalism.FourierDecayAlt.J.LocalKernelPSD := Formalism.FourierDecayAlt.P.local_kernel_psd
theorem jx_intersectionOfLocal : Formalism.FourierDecayAlt.J.IntersectionOfLocal := Formalism.FourierDecayAlt.P.intersection_of_local
theorem jx_latticeOfLocal : Formalism.FourierDecayAlt.J.LatticeOfLocal := Formalism.FourierDecayAlt.P.lattice_of_local
theorem jx_pullLatticeTyped : Formalism.FourierDecayAlt.J.PullLatticeTyped := Formalism.FourierDecayAlt.P.pull_lattice_typed
theorem jx_minShape : Formalism.FourierDecayAlt.J.MinShape := Formalism.FourierDecayAlt.P.minimum_shape
theorem jx_chebToThreshold : Formalism.FourierDecayAlt.J.ChebToThreshold := Formalism.FourierDecayAlt.P.chebyshev_to_threshold
theorem jx_thresholdBelow : Formalism.FourierDecayAlt.J.ThresholdBelow := Formalism.FourierDecayAlt.P.threshold_below
theorem jx_estimatesMono : Formalism.FourierDecayAlt.J.EstimatesMono := Formalism.FourierDecayAlt.P.estimates_mono
theorem jx_recursionGivesMassData : Formalism.FourierDecayAlt.J.RecursionGivesBounds := Formalism.FourierDecayAlt.P.recursion_gives_explicit_form
theorem jx_recursionGivesForm : Formalism.FourierDecayAlt.J.RecursionGivesForm := Formalism.FourierDecayAlt.P.recursion_gives_form
theorem jx_productOfE : Formalism.FourierDecayAlt.J.ProductOfE := Formalism.FourierDecayAlt.P.product_of_energies
theorem jx_topE : Formalism.FourierDecayAlt.J.TopE := Formalism.FourierDecayAlt.P.top_energy
theorem jx_onceOnly : Formalism.FourierDecayAlt.J.OnceOnly := Formalism.FourierDecayAlt.P.each_level_counted_once
theorem jx_formGivesMain : Formalism.FourierDecayAlt.J.FormGivesMain := Formalism.FourierDecayAlt.P.form_gives_theorem_A
theorem big_cell_recursion : Formalism.FourierDecayAlt.B2.BigCellRec := Formalism.FourierDecayAlt.P.bigCellRec_statement
theorem weylElementCommutesLevelOne_true : Formalism.FourierDecayAlt.B2.WeylElementCommutesLevelOne := Formalism.FourierDecayAlt.P.long_weyl_element_commutation
theorem unipotent_wb_recursion : Formalism.FourierDecayAlt.B2.UWbRec := Formalism.FourierDecayAlt.P.unipotent_weyl_recursion
theorem iterated_integral_identity : Formalism.FourierDecayAlt.B2.IterInt := Formalism.FourierDecayAlt.P.iterated_integration_formula
theorem iterated_integral_formula : Formalism.FourierDecayAlt.B2.AssembleIter := Formalism.FourierDecayAlt.P.iterated_integral_of_parts
theorem big_cell_factorization : Formalism.FourierDecayAlt.B2.BigCellFactor := Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization
theorem integral_constant_value : Formalism.FourierDecayAlt.B2.IntConst := Formalism.FourierDecayAlt.P.integration_formula_constant
theorem integral_norm : Formalism.FourierDecayAlt.B2.IntNorm := Formalism.FourierDecayAlt.P.integration_formula_normalisation_unique
theorem integral_norm_bound_variant_b : Formalism.FourierDecayAlt.B2.IntNormB := Formalism.FourierDecayAlt.P.normalisation_unique_every_setting
theorem g_n_integral_sharp : Formalism.FourierDecayAlt.B2.GNIntSharp := Formalism.FourierDecayAlt.P.norm_power_integrable_sharp
theorem integral_bound_all : Formalism.FourierDecayAlt.B2.CCIntAll := Formalism.FourierDecayAlt.P.matrix_coefficient_integrable_all
theorem b_setting_exists : Formalism.FourierDecayAlt.B2.RealPlaceDataExists := Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists
theorem admissible_setting_nonempty : Formalism.FourierDecayAlt.B2.RealPlaceDataNonempty := Formalism.FourierDecayAlt.P.setting_nonempty
theorem lemma_b_from_xi_function : Formalism.FourierDecayAlt.B2.LemmaBFromXi := Formalism.FourierDecayAlt.P.lemma_b_from_xi
theorem jx_pullLatticeTypedUnit : Formalism.FourierDecayAlt.J.PullLatticeTypedUnit := Formalism.FourierDecayAlt.P.pull_lattice_typed_unit
theorem jx_pullLiftTyped : Formalism.FourierDecayAlt.J.PullLiftTyped := Formalism.FourierDecayAlt.P.pull_lift_typed
theorem jx_pullLiftTypedUnit : Formalism.FourierDecayAlt.J.PullLiftTypedUnit := Formalism.FourierDecayAlt.P.pull_lift_typed_unit
theorem jx_topIsLocalKernel : Formalism.FourierDecayAlt.J.TopIsLocalKernel := Formalism.FourierDecayAlt.P.top_is_local_kernel
theorem jx_topUnitHeads : Formalism.FourierDecayAlt.J.TopUnitHeads := Formalism.FourierDecayAlt.P.top_unit_heads
theorem jx_diagPhase : Formalism.FourierDecayAlt.J.DiagPhase := Formalism.FourierDecayAlt.P.diagonal_phase_conj
theorem jx_blockDiagPSD : Formalism.FourierDecayAlt.J.BlockDiagPSD := Formalism.FourierDecayAlt.P.block_diagonal_psd
theorem oscillatory_reduction : Formalism.FourierDecayAlt.A6.OscReduction := Formalism.FourierDecayAlt.P.orbital_integral_change_of_variables
theorem gaussian_hessian : Formalism.FourierDecayAlt.A6.GaussHess := Formalism.FourierDecayAlt.P.gauss_hessian_index_exists
theorem stationary_phase : Formalism.FourierDecayAlt.A6.StationaryPhase := Formalism.FourierDecayAlt.P.padic_stationary_phase
theorem germ_phi : Formalism.FourierDecayAlt.A6.GermPhi := Formalism.FourierDecayAlt.P.germ_expansion_matrix_function
theorem germ_expansion : Formalism.FourierDecayAlt.A6.Germ := Formalism.FourierDecayAlt.P.germ_expansion_with_head
theorem germ_kernel : Formalism.FourierDecayAlt.A6.GermKernel := Formalism.FourierDecayAlt.P.germ_kernel_expansion
theorem germIdentity_true : Formalism.FourierDecayAlt.A6.GermIdentity := Formalism.FourierDecayAlt.P.germ_identity_bis
theorem thetaOmega_true : Formalism.FourierDecayAlt.A6.ThOm := Formalism.FourierDecayAlt.P.theta_omega_bound
theorem thetaExistence_recursion_true : Formalism.FourierDecayAlt.A5.ThetaExistsStep := Formalism.FourierDecayAlt.P.lattice_average_induction
theorem latticeAverage_true : Formalism.FourierDecayAlt.A5.LemmaA := Formalism.FourierDecayAlt.P.lattice_average_lemma_full
theorem pb_fourParts : Formalism.FourierDecayAlt.PB.FourParts := Formalism.FourierDecayAlt.P.four_parts
theorem pb_splitSum : Formalism.FourierDecayAlt.PB.SplitSum := Formalism.FourierDecayAlt.P.split_sum_alt
theorem pb_equalIota : Formalism.FourierDecayAlt.PB.GramSumLeOfPosSemidef := Formalism.FourierDecayAlt.P.equal_index
theorem pb_gGNumeric : Formalism.FourierDecayAlt.PB.GGNumeric := Formalism.FourierDecayAlt.P.gamma_numeric_bound
theorem pb_priceOfIota : Formalism.FourierDecayAlt.PB.NormSqBoundOfEqualIota := Formalism.FourierDecayAlt.P.price_of_index
theorem pb_pairSplit : Formalism.FourierDecayAlt.PB.PairSplit := Formalism.FourierDecayAlt.P.pair_split_alt
theorem pb_subFamily : Formalism.FourierDecayAlt.PB.SubFamily := Formalism.FourierDecayAlt.P.subfamilyAlt
theorem pb_loopsGiveRows : Formalism.FourierDecayAlt.PB.LoopsGiveRows := Formalism.FourierDecayAlt.P.loops_give_series
theorem pb_nGTotal : Formalism.FourierDecayAlt.PB.NGTotal := Formalism.FourierDecayAlt.P.total_count_bound
theorem pb_textClosing : Formalism.FourierDecayAlt.PB.NormSqAddBoundBySqrtSum := Formalism.FourierDecayAlt.P.text_closing
theorem pb_pairBoundAbstract : Formalism.FourierDecayAlt.PB.PairBoundAbstract := Formalism.FourierDecayAlt.P.pair_bound_abstract
theorem pb_numPrice : Formalism.FourierDecayAlt.PB.NumPrice := Formalism.FourierDecayAlt.P.numerical_price
theorem pb_numExp : Formalism.FourierDecayAlt.PB.NumExp := Formalism.FourierDecayAlt.P.numerical_exponent
theorem pb_numDens : Formalism.FourierDecayAlt.PB.NumDens := Formalism.FourierDecayAlt.P.numerical_density
theorem pb_numLoops : Formalism.FourierDecayAlt.PB.NumLoops := Formalism.FourierDecayAlt.P.numerical_loops
theorem pb_numNG : Formalism.FourierDecayAlt.PB.NumNG := Formalism.FourierDecayAlt.P.numerical_count
theorem pb_nGExponent : Formalism.FourierDecayAlt.PB.NGExponent := Formalism.FourierDecayAlt.P.count_exponent
theorem pb_etaZero : Formalism.FourierDecayAlt.PB.SqrtSumSqLeOneAddInvPowSix := Formalism.FourierDecayAlt.P.eta_zero_alt
theorem pb_mainRowShape : Formalism.FourierDecayAlt.PB.MainRowShape := Formalism.FourierDecayAlt.P.principal_series_shape
theorem pb_pairBound : Formalism.FourierDecayAlt.PB.PairBound := Formalism.FourierDecayAlt.P.pair_bound_alt
theorem pb_axiomsOfLocalModel : Formalism.FourierDecayAlt.PB.AxiomsOfLocalModel := Formalism.FourierDecayAlt.P.axioms_of_local_model
theorem pb_mainRow : Formalism.FourierDecayAlt.PB.MainRow := Formalism.FourierDecayAlt.P.principal_series
theorem pb_loopsJoint : Formalism.FourierDecayAlt.PB.LoopsJoint := Formalism.FourierDecayAlt.P.loops_joint
theorem pb_pairBoundFromLocal : Formalism.FourierDecayAlt.PB.PairBoundFromLocal := Formalism.FourierDecayAlt.P.pair_bound_from_local
theorem mx_levFns : Formalism.FourierDecayAlt.M.LevFns := Formalism.FourierDecayAlt.P.level_function_relations
theorem mx_levP : Formalism.FourierDecayAlt.M.LevP := Formalism.FourierDecayAlt.P.level_p_relations
theorem mx_levPb : Formalism.FourierDecayAlt.M.LevPb := Formalism.FourierDecayAlt.P.level_pb_relations
theorem mx_levPP : Formalism.FourierDecayAlt.M.LevPP := Formalism.FourierDecayAlt.P.level_pp_relations
theorem mx_levNab : Formalism.FourierDecayAlt.M.LevNab := Formalism.FourierDecayAlt.P.level_nabla_relations
theorem mx_levNabs : Formalism.FourierDecayAlt.M.LevNabs := Formalism.FourierDecayAlt.P.level_nabla_star_relations
theorem mx_levelExists : Formalism.FourierDecayAlt.M.LevelExists := Formalism.FourierDecayAlt.P.level_exists_model
theorem mx_levelAssemble : Formalism.FourierDecayAlt.M.LevelAssemble := Formalism.FourierDecayAlt.P.level_assemble
theorem mx_mulOpHom : Formalism.FourierDecayAlt.M.MulOpHom := Formalism.FourierDecayAlt.P.multiplication_op_hom
theorem mx_eulerLeibniz : Formalism.FourierDecayAlt.M.EulerLeibniz := Formalism.FourierDecayAlt.P.euler_leibniz
theorem mx_eulerCoord : Formalism.FourierDecayAlt.M.EulerCoord := Formalism.FourierDecayAlt.P.euler_coordinates
theorem mx_eulerComm : Formalism.FourierDecayAlt.M.EulerComm := Formalism.FourierDecayAlt.P.euler_commute
theorem mx_eulerMul : Formalism.FourierDecayAlt.M.EulerMul := Formalism.FourierDecayAlt.P.eulerMul_statement
theorem mx_fnNonzero : Formalism.FourierDecayAlt.M.FnNonzero := Formalism.FourierDecayAlt.P.function_nonzero
theorem mx_modelNontrivial : Formalism.FourierDecayAlt.M.ModelNontrivial := Formalism.FourierDecayAlt.P.model_nontrivial
theorem mx_starGens : Formalism.FourierDecayAlt.M.StarGens := Formalism.FourierDecayAlt.P.star_generators
theorem mx_levelStar : Formalism.FourierDecayAlt.M.LevelStar := Formalism.FourierDecayAlt.P.level_star
theorem mx_modelWordsAssemble : Formalism.FourierDecayAlt.M.ModelWordsAssemble := Formalism.FourierDecayAlt.P.model_words_assemble
theorem mx_cutAdm : Formalism.FourierDecayAlt.M.CutAdm := Formalism.FourierDecayAlt.P.cut_admissible
theorem mx_cutAdmBase : Formalism.FourierDecayAlt.M.CutAdmBase := Formalism.FourierDecayAlt.P.cut_admissible_base
theorem mx_modelAssemble : Formalism.FourierDecayAlt.M.ModelAssemble := Formalism.FourierDecayAlt.P.model_assemble
theorem mx_modelAssembleBase : Formalism.FourierDecayAlt.M.ModelAssembleBase := Formalism.FourierDecayAlt.P.model_assemble_base
theorem mx_tyInterlaces : Formalism.FourierDecayAlt.M.TyInterlaces := Formalism.FourierDecayAlt.P.types_interlace
theorem mx_tyComplete : Formalism.FourierDecayAlt.M.TyComplete := Formalism.FourierDecayAlt.P.types_complete
theorem mx_rhoUp : Formalism.FourierDecayAlt.M.RhoUp := Formalism.FourierDecayAlt.P.rho_raise
theorem mx_nrmFacts : Formalism.FourierDecayAlt.M.NrmFacts := Formalism.FourierDecayAlt.P.nrmFacts_statement
theorem mx_realPoints : Formalism.FourierDecayAlt.M.RealPoints := Formalism.FourierDecayAlt.P.realPoints_statement
theorem mx_wExact : Formalism.FourierDecayAlt.M.WExact := Formalism.FourierDecayAlt.P.weight_exact
theorem mx_interlaceSignTwo : Formalism.FourierDecayAlt.M.InterlaceSignTwo := Formalism.FourierDecayAlt.P.interlace_sign_two
theorem mx_sSScalar : Formalism.FourierDecayAlt.M.SSScalar := Formalism.FourierDecayAlt.P.shift_scalar_relation
theorem mx_sSShift : Formalism.FourierDecayAlt.M.SSShift := Formalism.FourierDecayAlt.P.shift_shift_relation
theorem mx_sSNorm : Formalism.FourierDecayAlt.M.SSNorm := Formalism.FourierDecayAlt.P.shift_norm_relation
theorem mx_sSComm : Formalism.FourierDecayAlt.M.SSComm := Formalism.FourierDecayAlt.P.shift_commute_relation
theorem mx_sSMixed : Formalism.FourierDecayAlt.M.SSMixed := Formalism.FourierDecayAlt.P.shift_mixed_relation
theorem mx_nabSS : Formalism.FourierDecayAlt.M.NabSS := Formalism.FourierDecayAlt.P.nabla_shift_relation
theorem mx_curvature : Formalism.FourierDecayAlt.M.Curvature := Formalism.FourierDecayAlt.P.m_curvature_proof
theorem pb_pullLatticeOrdinary : Formalism.FourierDecayAlt.PB.PullLatticeOrdinary := Formalism.FourierDecayAlt.P.pull_lattice_ordinary
theorem pb_latticeLink : Formalism.FourierDecayAlt.PB.LatticeLink := Formalism.FourierDecayAlt.P.lattice_link
theorem mx_qQNormal : Formalism.FourierDecayAlt.M.QQNormal := Formalism.FourierDecayAlt.P.transfer_normal_alt
theorem mx_qQHerm : Formalism.FourierDecayAlt.M.QQHerm := Formalism.FourierDecayAlt.P.transfer_hermitian
theorem mx_qQLeading : Formalism.FourierDecayAlt.M.QQLeading := Formalism.FourierDecayAlt.P.transfer_leading
theorem mx_qQZeta : Formalism.FourierDecayAlt.M.QQZeta := Formalism.FourierDecayAlt.P.transfer_zeta
theorem mx_startIsStartAssemble : Formalism.FourierDecayAlt.M.StartIsStartAssemble := Formalism.FourierDecayAlt.P.start_module_assemble
theorem mx_startAssemble : Formalism.FourierDecayAlt.M.StartAssemble := Formalism.FourierDecayAlt.P.start_assemble
theorem mx_sitesOKM : Formalism.FourierDecayAlt.M.SitesOKM := Formalism.FourierDecayAlt.P.sites_admissible_model
theorem mx_siteJoint : Formalism.FourierDecayAlt.M.SiteJoint := Formalism.FourierDecayAlt.P.site_joint
theorem mx_chainM : Formalism.FourierDecayAlt.M.ChainM := Formalism.FourierDecayAlt.P.model_chain
theorem mx_lowerCommutes : Formalism.FourierDecayAlt.M.LowerCommutes := Formalism.FourierDecayAlt.P.lower_commutes
theorem mx_qQRTTEntries : Formalism.FourierDecayAlt.M.QQRTTEntries := Formalism.FourierDecayAlt.P.transfer_rtt_entries
theorem mx_qQRTT : Formalism.FourierDecayAlt.M.QQRTT := Formalism.FourierDecayAlt.P.transfer_rtt
theorem mx_qQRTTOfEntries : Formalism.FourierDecayAlt.M.QQRTTOfEntries := Formalism.FourierDecayAlt.P.transfer_rtt_of_entries
theorem mx_qQDet : Formalism.FourierDecayAlt.M.QQDet := Formalism.FourierDecayAlt.P.transfer_determinant
theorem commutator_relation_of_transvections : Formalism.FourierDecayAlt.M.T21Commute := Formalism.FourierDecayAlt.P.lower_left_commute_model
theorem mx_startIsStart : Formalism.FourierDecayAlt.M.StartIsStart := Formalism.FourierDecayAlt.P.start_matrix_is_module
theorem mx_startOK : Formalism.FourierDecayAlt.M.StartOK := Formalism.FourierDecayAlt.P.start_admissible_model
theorem mx_lowerStart : Formalism.FourierDecayAlt.M.LowerStart := Formalism.FourierDecayAlt.P.lower_levels_same_scalar
theorem mx_modelWords : Formalism.FourierDecayAlt.M.ModelWords := Formalism.FourierDecayAlt.P.model_words_all_levels
theorem mx_modelFrame : Formalism.FourierDecayAlt.M.ModelFrame := Formalism.FourierDecayAlt.P.model_frame
theorem mx_modelFrameBase : Formalism.FourierDecayAlt.M.ModelFrameBase := Formalism.FourierDecayAlt.P.model_frame_base
theorem pn_normBound : Formalism.FourierDecayAlt.PN.NormBound := Formalism.FourierDecayAlt.P.pn_norm_bound
theorem pn_normOfMain : Formalism.FourierDecayAlt.PN.NormOfMain := Formalism.FourierDecayAlt.P.norm_of_leading_term
theorem pn_normOfLemmas : Formalism.FourierDecayAlt.PN.NormOfLemmas := Formalism.FourierDecayAlt.P.norm_of_lemmas
theorem pn_framePassage : Formalism.FourierDecayAlt.PN.FramePassage := Formalism.FourierDecayAlt.P.frame_passage
theorem pn_normRe : Formalism.FourierDecayAlt.PN.NormRe := Formalism.FourierDecayAlt.P.norm_real_part
theorem pn_zpowForm : Formalism.FourierDecayAlt.PN.ZpowForm := Formalism.FourierDecayAlt.P.pn_zpow_form
theorem pn_meanAmpJoint : Formalism.FourierDecayAlt.PN.MeanAmpJoint := Formalism.FourierDecayAlt.P.mean_amplitude_joint
theorem pn_classSquaresSum : Formalism.FourierDecayAlt.PN.ClassSquaresSum := Formalism.FourierDecayAlt.P.class_squares_sum
theorem pn_classCS : Formalism.FourierDecayAlt.PN.ClassCS := Formalism.FourierDecayAlt.P.class_cauchy_schwarz
theorem pn_firstBracket : Formalism.FourierDecayAlt.PN.FirstBracket := Formalism.FourierDecayAlt.P.first_bracket
theorem pn_secondBracket : Formalism.FourierDecayAlt.PN.SecondBracket := Formalism.FourierDecayAlt.P.second_bracket
theorem pn_rowFromClasses : Formalism.FourierDecayAlt.PN.RowFromClasses := Formalism.FourierDecayAlt.P.line_from_classes
theorem pn_genMassOfSplit : Formalism.FourierDecayAlt.PN.GenMassOfSplit := Formalism.FourierDecayAlt.P.general_mass_of_split
theorem pn_rowNGAbstract : Formalism.FourierDecayAlt.PN.RowNGAbstract := Formalism.FourierDecayAlt.P.line_norm_abstract
theorem pn_exponentSum : Formalism.FourierDecayAlt.PN.ExponentSum := Formalism.FourierDecayAlt.P.exponent_sum
theorem pn_exponentSumText : Formalism.FourierDecayAlt.PN.ExponentSumText := Formalism.FourierDecayAlt.P.exponent_sum_explicit
theorem pn_nGNumbers : Formalism.FourierDecayAlt.PN.NGNumbers := Formalism.FourierDecayAlt.P.norm_numbers
theorem pn_rowNGJoint : Formalism.FourierDecayAlt.PN.RowNGJoint := Formalism.FourierDecayAlt.P.line_norm_joint
theorem pn_pairBoundFromLocalNG : Formalism.FourierDecayAlt.PN.PairBoundFromLocalNG := Formalism.FourierDecayAlt.P.pair_bound_from_local_norm
theorem qx_modelIsNF : Formalism.FourierDecayAlt.Q.ModelIsNF := Formalism.FourierDecayAlt.P.model_is_normal_form
theorem ux_sliceRight : Formalism.FourierDecayAlt.U.SliceRight := Formalism.FourierDecayAlt.P.slice_right_coordinates
theorem ux_sliceLeft : Formalism.FourierDecayAlt.U.SliceLeft := Formalism.FourierDecayAlt.P.slice_left_coordinates
theorem ux_sliceZ : Formalism.FourierDecayAlt.U.SliceZ := Formalism.FourierDecayAlt.P.slice_z_coordinates
theorem ux_directionsInP : Formalism.FourierDecayAlt.U.DirectionsInP := Formalism.FourierDecayAlt.P.directions_in_parabolic
theorem ux_zjAffine : Formalism.FourierDecayAlt.U.ZjAffine := Formalism.FourierDecayAlt.P.level_z_affine
theorem ux_budgetWord : Formalism.FourierDecayAlt.U.BudgetWord := Formalism.FourierDecayAlt.P.budget_word
theorem ux_budgetWordStar : Formalism.FourierDecayAlt.U.BudgetWordStar := Formalism.FourierDecayAlt.P.budget_word_star
theorem budget_second_unipotent : Formalism.FourierDecayAlt.U.DerivativeBudgetCount := Formalism.FourierDecayAlt.P.budget_second_corollary
theorem thresholds_second_unipotent : Formalism.FourierDecayAlt.U.GermThresholds := Formalism.FourierDecayAlt.P.thresholds_second_corollary
theorem ux_budgetTop : Formalism.FourierDecayAlt.U.BudgetTop := Formalism.FourierDecayAlt.P.budget_top_level
theorem ux_budgetTopConv : Formalism.FourierDecayAlt.U.BudgetTopConv := Formalism.FourierDecayAlt.P.budget_top_convergence
theorem ux_decayMin : Formalism.FourierDecayAlt.U.DecayMin := Formalism.FourierDecayAlt.P.decay_minimum
theorem ux_scaleMatch : Formalism.FourierDecayAlt.U.ScaleMatch := Formalism.FourierDecayAlt.P.scale_matching
theorem ux_powerMatch : Formalism.FourierDecayAlt.U.PowerMatch := Formalism.FourierDecayAlt.P.power_matching
theorem ux_derivBoundOfDecay : Formalism.FourierDecayAlt.U.DerivBoundOfDecay := Formalism.FourierDecayAlt.P.derivative_bound_of_decay
theorem ux_derivBoundComp : Formalism.FourierDecayAlt.U.DerivBoundComp := Formalism.FourierDecayAlt.P.derivative_bound_composition
theorem ux_cCMono : Formalism.FourierDecayAlt.U.CCMono := Formalism.FourierDecayAlt.P.compactly_supported_monotone
theorem ux_seminormOfForm : Formalism.FourierDecayAlt.U.SeminormOfForm := Formalism.FourierDecayAlt.P.seminorm_of_form
theorem ux_seminormCompletion : Formalism.FourierDecayAlt.U.SeminormCompletion := Formalism.FourierDecayAlt.P.seminorm_completion
theorem ux_starPi : Formalism.FourierDecayAlt.U.StarPi := Formalism.FourierDecayAlt.P.star_projection
theorem ux_phiSuppGOfParts : Formalism.FourierDecayAlt.U.PhiSuppGOfParts := Formalism.FourierDecayAlt.P.phi_support_level_of_parts
theorem unipotent_corollary_of_parts : Formalism.FourierDecayAlt.U.GermExpansionHypothesisFromComponents := Formalism.FourierDecayAlt.P.corollary_u2_of_parts
theorem ux_useDerivBoundOfParts : Formalism.FourierDecayAlt.U.UseDerivBoundOfParts := Formalism.FourierDecayAlt.P.derivative_bound_use_of_parts
theorem ux_useGermOfParts : Formalism.FourierDecayAlt.U.UseGermOfParts := Formalism.FourierDecayAlt.P.germ_expansion_of_parts
theorem ux_useGermTopOfParts : Formalism.FourierDecayAlt.U.UseGermTopOfParts := Formalism.FourierDecayAlt.P.germ_top_level_of_parts
theorem ux_useGermTopCountOfParts : Formalism.FourierDecayAlt.U.UseGermTopCountOfParts := Formalism.FourierDecayAlt.P.germ_top_count_of_parts
theorem ux_germInFormOfParts : Formalism.FourierDecayAlt.U.GermInFormOfParts := Formalism.FourierDecayAlt.P.germ_in_form_of_parts
theorem unipotent_sizes_bound_of_parts : Formalism.FourierDecayAlt.U.CoordinateSizesFromComponents := Formalism.FourierDecayAlt.P.coordinate_sizes_of_parts
theorem coordinateDecay_of_sizes : Formalism.FourierDecayAlt.U.CoordinateDecayOfSizes := Formalism.FourierDecayAlt.P.norm_decay_of_coordinate_sizes
theorem weightIntegrable_true : Formalism.FourierDecayAlt.U.WeightIntegrable := Formalism.FourierDecayAlt.P.weight_integrability
theorem ux_intTop : Formalism.FourierDecayAlt.U.IntTop := Formalism.FourierDecayAlt.P.integrability_top_level
theorem lex_thetaForm : Formalism.FourierDecayAlt.LE.ThetaForm := Formalism.FourierDecayAlt.P.le_thetaForm_proof
theorem lex_thetaRange : Formalism.FourierDecayAlt.LE.ThetaRange := Formalism.FourierDecayAlt.P.le_thetaRange_proof
theorem lex_thetaSmooth : Formalism.FourierDecayAlt.LE.ThetaSmooth := Formalism.FourierDecayAlt.P.le_thetaSmooth_proof
theorem lex_thetaBound : Formalism.FourierDecayAlt.LE.ThetaBound := Formalism.FourierDecayAlt.P.le_thetaBound_proof
theorem lex_thetaLimit : Formalism.FourierDecayAlt.LE.ThetaLimit := Formalism.FourierDecayAlt.P.theta_limit
theorem lex_thetaMono : Formalism.FourierDecayAlt.LE.ThetaMono := Formalism.FourierDecayAlt.P.le_thetaMono_proof
theorem lex_cutBound : Formalism.FourierDecayAlt.LE.CutBound := Formalism.FourierDecayAlt.P.cutoff_bound
theorem lex_cutTheta : Formalism.FourierDecayAlt.LE.CutTheta := Formalism.FourierDecayAlt.P.cutoff_theta
theorem lex_leibniz : Formalism.FourierDecayAlt.LE.Leibniz := Formalism.FourierDecayAlt.P.leibniz_rule
theorem lex_termZero : Formalism.FourierDecayAlt.LE.TermZero := Formalism.FourierDecayAlt.P.le_termZero_proof
theorem lex_dsMeas : Formalism.FourierDecayAlt.LE.DsMeas := Formalism.FourierDecayAlt.P.measure_measurable
theorem lex_coefIntegrable : Formalism.FourierDecayAlt.LE.CoefIntegrable := Formalism.FourierDecayAlt.P.coefficient_integrable
theorem lex_adj : Formalism.FourierDecayAlt.LE.Adj := Formalism.FourierDecayAlt.P.adjoint_identity
theorem lex_eFinite : Formalism.FourierDecayAlt.LE.EFinite := Formalism.FourierDecayAlt.P.energy_finite
theorem lex_cSTerm : Formalism.FourierDecayAlt.LE.CSTerm := Formalism.FourierDecayAlt.P.cauchy_schwarz_term
theorem lex_shiftBound : Formalism.FourierDecayAlt.LE.ShiftBound := Formalism.FourierDecayAlt.P.le_shiftBound_proof
theorem lex_markovTerm : Formalism.FourierDecayAlt.LE.MarkovTerm := Formalism.FourierDecayAlt.P.markov_term
theorem lex_termBound : Formalism.FourierDecayAlt.LE.TermBound := Formalism.FourierDecayAlt.P.le_termBound_proof
theorem lex_geomSum : Formalism.FourierDecayAlt.LE.GeomSum := Formalism.FourierDecayAlt.P.geometric_sum_bound
theorem lex_energyStep : Formalism.FourierDecayAlt.LE.EnergyStep := Formalism.FourierDecayAlt.P.energy_estimate
theorem lex_absorb : Formalism.FourierDecayAlt.LE.Absorb := Formalism.FourierDecayAlt.P.absorb_term
theorem lex_uniformBound : Formalism.FourierDecayAlt.LE.UniformBound := Formalism.FourierDecayAlt.P.le_uniformBound_proof
theorem lex_fatouStep : Formalism.FourierDecayAlt.LE.FatouStep := Formalism.FourierDecayAlt.P.fatou_estimate
theorem lex_domConv : Formalism.FourierDecayAlt.LE.DomConv := Formalism.FourierDecayAlt.P.dominated_convergence
theorem lex_stepClaim : Formalism.FourierDecayAlt.LE.StepClaim := Formalism.FourierDecayAlt.P.energy_estimate_of_lemmas
theorem lex_stepClaimFromSteps : Formalism.FourierDecayAlt.LE.StepClaimFromSteps := Formalism.FourierDecayAlt.P.energy_estimate_from_parts
theorem coefficient_square_summable : Formalism.FourierDecayAlt.LE.InterpolationCoefficientsInL2 := Formalism.FourierDecayAlt.P.le_interpolation_coefficients_in_L2
theorem lex_limitA : Formalism.FourierDecayAlt.LE.LimitA := Formalism.FourierDecayAlt.P.limit_A
theorem limit_l2 : Formalism.FourierDecayAlt.LE.CutoffLimitInL2 := Formalism.FourierDecayAlt.P.le_cutoff_limit_in_L2
theorem lex_pairLimit : Formalism.FourierDecayAlt.LE.PairLimit := Formalism.FourierDecayAlt.P.pair_limit
theorem lex_limitB : Formalism.FourierDecayAlt.LE.LimitB := Formalism.FourierDecayAlt.P.limit_B
theorem lex_gridConvergence : Formalism.FourierDecayAlt.LE.GridConvergence := Formalism.FourierDecayAlt.P.grid_convergence
theorem lex_constSign : Formalism.FourierDecayAlt.LE.ConstSign := Formalism.FourierDecayAlt.P.constant_sign
theorem lex_pRatioMiddle : Formalism.FourierDecayAlt.LE.PRatioMiddle := Formalism.FourierDecayAlt.P.ratio_middle_range
theorem lex_constants : Formalism.FourierDecayAlt.LE.Constants := Formalism.FourierDecayAlt.P.constants_choice
theorem lex_boxesFit : Formalism.FourierDecayAlt.LE.BoxesFit := Formalism.FourierDecayAlt.P.boxes_fit
theorem lex_pImportsHold : Formalism.FourierDecayAlt.LE.PImportsHold := Formalism.FourierDecayAlt.P.imported_results_hold
theorem lex_reduceToBoxes : Formalism.FourierDecayAlt.LE.ReduceToBoxes := Formalism.FourierDecayAlt.P.reduce_to_boxes
theorem lex_claimInduction : Formalism.FourierDecayAlt.LE.ClaimInduction := Formalism.FourierDecayAlt.P.level_induction
theorem lex_claimAll : Formalism.FourierDecayAlt.LE.ClaimAll := Formalism.FourierDecayAlt.P.induction_all_levels
theorem lex_boxLimitFromClaim : Formalism.FourierDecayAlt.LE.BoxLimitFromClaim := Formalism.FourierDecayAlt.P.box_limit_of_induction
theorem lex_lemmaE : Formalism.FourierDecayAlt.LE.LemmaE := Formalism.FourierDecayAlt.P.le_E_proof
theorem lex_lemmaEFromSteps : Formalism.FourierDecayAlt.LE.LemmaEFromSteps := Formalism.FourierDecayAlt.P.lemma_E_of_parts
theorem e_prime_l2 : Formalism.FourierDecayAlt.LE.WeightedIntegrable := Formalism.FourierDecayAlt.P.le_weightedIntegrable_proof
theorem lex_epCoefInt : Formalism.FourierDecayAlt.LE.EpCoefInt := Formalism.FourierDecayAlt.P.derived_coefficient_integrable
theorem lex_epStep5 : Formalism.FourierDecayAlt.LE.EpStep5 := Formalism.FourierDecayAlt.P.derived_energy_fifth_estimate
theorem lex_epStep6 : Formalism.FourierDecayAlt.LE.EpStep6 := Formalism.FourierDecayAlt.P.derived_energy_sixth_estimate
theorem lex_lemmaEprime : Formalism.FourierDecayAlt.LE.LemmaEprime := Formalism.FourierDecayAlt.P.lemma_E_derived
theorem lex_lemmaEprimeFull : Formalism.FourierDecayAlt.LE.LemmaEprimeFull := Formalism.FourierDecayAlt.P.lemma_E_derived_full
theorem lex_lemmaEprimeFromSteps : Formalism.FourierDecayAlt.LE.LemmaEprimeFromSteps := Formalism.FourierDecayAlt.P.lemma_E_derived_of_parts
theorem lex_estEJoint : Formalism.FourierDecayAlt.LE.EstEJoint := Formalism.FourierDecayAlt.P.energy_estimate_joint
theorem ux_weakToStrong : Formalism.FourierDecayAlt.U.WeakToStrong := Formalism.FourierDecayAlt.P.weak_to_strong_smoothness
theorem ux_theoremUOfParts : Formalism.FourierDecayAlt.U.TheoremUOfParts := Formalism.FourierDecayAlt.P.theorem_u_of_parts
theorem ux_cCModelExists : Formalism.FourierDecayAlt.U.CCModelExists := Formalism.FourierDecayAlt.P.compactly_supported_banach_model
theorem sizes_first_unipotent : Formalism.FourierDecayAlt.U.BigCellCoordinateSizes := Formalism.FourierDecayAlt.P.block3_apply_embedding
theorem sizes_second_unipotent : Formalism.FourierDecayAlt.U.BlockHeadSizes := Formalism.FourierDecayAlt.P.aux_statement_17
theorem ux_sizesTop : Formalism.FourierDecayAlt.U.SizesTop := Formalism.FourierDecayAlt.P.sizes_top_level
theorem ux_zhSlice : Formalism.FourierDecayAlt.U.ZhSlice := Formalism.FourierDecayAlt.P.hat_z_on_slice
theorem ux_detZj : Formalism.FourierDecayAlt.U.DetZj := Formalism.FourierDecayAlt.P.level_determinant_z
theorem ux_zhDmin : Formalism.FourierDecayAlt.U.ZhDmin := Formalism.FourierDecayAlt.P.hat_z_minimum_degree
theorem ux_gfSlice : Formalism.FourierDecayAlt.U.GfSlice := Formalism.FourierDecayAlt.P.level_function_slice
theorem ux_bigCellBij : Formalism.FourierDecayAlt.U.BigCellBij := Formalism.FourierDecayAlt.P.big_cell_bijection
theorem ux_topCells : Formalism.FourierDecayAlt.U.TopCells := Formalism.FourierDecayAlt.P.top_cells
theorem ux_topCellsOfParts : Formalism.FourierDecayAlt.U.TopCellsOfParts := Formalism.FourierDecayAlt.P.top_cells_of_parts
theorem qx_tTriples : Formalism.FourierDecayAlt.Q.TTriples := Formalism.FourierDecayAlt.P.transfer_triples
theorem qx_leading : Formalism.FourierDecayAlt.Q.Leading := Formalism.FourierDecayAlt.P.leading_term_alt
theorem qx_tLinLoc : Formalism.FourierDecayAlt.Q.TLinLoc := Formalism.FourierDecayAlt.P.transfer_linear_local
theorem qx_tJointSmooth : Formalism.FourierDecayAlt.Q.TJointSmooth := Formalism.FourierDecayAlt.P.transfer_joint_smooth
theorem qx_famOps : Formalism.FourierDecayAlt.Q.FamOps := Formalism.FourierDecayAlt.P.family_operators
theorem qx_resGFam : Formalism.FourierDecayAlt.Q.ResGFam := Formalism.FourierDecayAlt.P.restriction_good_family
theorem qx_resMem : Formalism.FourierDecayAlt.Q.ResMem := Formalism.FourierDecayAlt.P.restriction_mem
theorem qx_expFirstCol : Formalism.FourierDecayAlt.Q.ExpFirstCol := Formalism.FourierDecayAlt.P.expansion_first_column
theorem qx_expLastCol : Formalism.FourierDecayAlt.Q.ExpLastCol := Formalism.FourierDecayAlt.P.expansion_last_column
theorem qx_expFirstRow : Formalism.FourierDecayAlt.Q.ExpFirstRow := Formalism.FourierDecayAlt.P.expansion_first_line
theorem qx_expLastRow : Formalism.FourierDecayAlt.Q.ExpLastRow := Formalism.FourierDecayAlt.P.expansion_last_line
theorem qx_rowForm : Formalism.FourierDecayAlt.Q.RowForm := Formalism.FourierDecayAlt.P.line_form_of_minor
theorem qx_skipSucc : Formalism.FourierDecayAlt.Q.SkipSucc := Formalism.FourierDecayAlt.P.skip_succ_identity
theorem qx_skipSucc2 : Formalism.FourierDecayAlt.Q.SkipSucc2 := Formalism.FourierDecayAlt.P.skip_succ_double_identity
theorem qx_starMinor : Formalism.FourierDecayAlt.Q.StarMinor := Formalism.FourierDecayAlt.P.star_quantum_minor
theorem qx_rTTIndependence : Formalism.FourierDecayAlt.Q.RTTIndependence := Formalism.FourierDecayAlt.P.rtt_independence
theorem qx_lemmaD : Formalism.FourierDecayAlt.Q.LemmaD := Formalism.FourierDecayAlt.P.lemma_d_determinant_identity
theorem qx_contractionsCovariant : Formalism.FourierDecayAlt.Q.ContractionsCovariant := Formalism.FourierDecayAlt.P.contractions_covariant
theorem first_contraction_adapted₂ : Formalism.FourierDecayAlt.Q.ChatAdapted := Formalism.FourierDecayAlt.P.first_contraction_adapted
theorem second_contraction_adapted₂ : Formalism.FourierDecayAlt.Q.Chat2Adapted := Formalism.FourierDecayAlt.P.second_contraction_adapted
theorem qx_eabGlLev : Formalism.FourierDecayAlt.Q.EabGlLev := Formalism.FourierDecayAlt.P.generator_gl_level
theorem qx_eabPres : Formalism.FourierDecayAlt.Q.EabPres := Formalism.FourierDecayAlt.P.generator_action_preserved
theorem qx_fFZero : Formalism.FourierDecayAlt.Q.FFZero := Formalism.FourierDecayAlt.P.fusion_form_vanishes
theorem qx_qMinorLeftH : Formalism.FourierDecayAlt.Q.QMinorLeftH := Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian
theorem qx_rdSkew : Formalism.FourierDecayAlt.Q.RdSkew := Formalism.FourierDecayAlt.P.right_differential_skew
theorem qx_ruleRight : Formalism.FourierDecayAlt.Q.RuleRight := Formalism.FourierDecayAlt.P.right_action_rule
theorem qx_vMonic : Formalism.FourierDecayAlt.Q.VMonic := Formalism.FourierDecayAlt.P.capelli_polynomial_monic
theorem qx_w1Facts : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts := Formalism.FourierDecayAlt.P.weyl_level_element_properties
theorem qx_yLeibniz : Formalism.FourierDecayAlt.Q.YLeibniz := Formalism.FourierDecayAlt.P.twisted_leibniz_rule
theorem qx_capLZero : Formalism.FourierDecayAlt.Q.CapLZero := Formalism.FourierDecayAlt.P.capelli_level_zero
theorem qx_tLZero : Formalism.FourierDecayAlt.Q.TLZero := Formalism.FourierDecayAlt.P.operator_level_zero
theorem ux_hpkBlocks : Formalism.FourierDecayAlt.U.HpkBlocks := Formalism.FourierDecayAlt.P.hermitian_group_blocks
theorem ux_sliceMem : Formalism.FourierDecayAlt.U.SliceMem := Formalism.FourierDecayAlt.P.slice_membership
theorem ux_radicalParam : Formalism.FourierDecayAlt.U.RadicalParam := Formalism.FourierDecayAlt.P.radical_parametrisation
theorem ux_lowWSpec : Formalism.FourierDecayAlt.U.LowWSpec := Formalism.FourierDecayAlt.P.low_weight_specialisation
theorem ux_headOrbit : Formalism.FourierDecayAlt.U.HeadOrbit := Formalism.FourierDecayAlt.P.head_orbit
theorem ux_charBlock : Formalism.FourierDecayAlt.U.CharBlock := Formalism.FourierDecayAlt.P.character_on_blocks
theorem ux_cornerInv : Formalism.FourierDecayAlt.U.CornerInv := Formalism.FourierDecayAlt.P.corner_inverse
theorem qx_rTTLevelFromUpper : Formalism.FourierDecayAlt.Q.RTTLevelFromUpper := Formalism.FourierDecayAlt.P.rtt_level_from_upper
theorem qx_resSurj : Formalism.FourierDecayAlt.Q.ResSurj := Formalism.FourierDecayAlt.P.resSurj_statement
theorem qx_cellDecomp : Formalism.FourierDecayAlt.Q.CellDecomp := Formalism.FourierDecayAlt.P.cell_decomposition
theorem qx_cellDense : Formalism.FourierDecayAlt.Q.CellDense := Formalism.FourierDecayAlt.P.cells_dense
theorem qx_fFTransfer : Formalism.FourierDecayAlt.Q.FFTransfer := Formalism.FourierDecayAlt.P.flag_frame_transfer
theorem pointwiseIntegralBound_of_components : Formalism.FourierDecayAlt.U.PointwiseIntegralBoundFromComponents := Formalism.FourierDecayAlt.P.phi_bound_of_parts
theorem ux_phiSupport : Formalism.FourierDecayAlt.U.PhiSupport := Formalism.FourierDecayAlt.P.phi_support_determinant
theorem qx_eigenCoeff : Formalism.FourierDecayAlt.Q.EigenCoeff := Formalism.FourierDecayAlt.P.casimir_eigenvalue_coefficients
theorem derivativeCost_true : Formalism.FourierDecayAlt.U.DerivativeCost := Formalism.FourierDecayAlt.P.derivative_cost_bound
theorem qx_rTTUpperFromSteps : Formalism.FourierDecayAlt.Q.RTTUpperFromSteps := Formalism.FourierDecayAlt.P.rtt_upper_relations_from_descent
theorem qx_qdetFromRTT : Formalism.FourierDecayAlt.Q.QdetFromRTT := Formalism.FourierDecayAlt.P.quantum_determinant_from_rtt
theorem qx_borderE : Formalism.FourierDecayAlt.Q.BorderE := Formalism.FourierDecayAlt.P.border_first_expansion
theorem qx_borderS : Formalism.FourierDecayAlt.Q.BorderS := Formalism.FourierDecayAlt.P.border_last_expansion
theorem qx_borderFull : Formalism.FourierDecayAlt.Q.BorderFull := Formalism.FourierDecayAlt.P.border_full_expansion
theorem qx_moveVec : Formalism.FourierDecayAlt.Q.MoveVec := Formalism.FourierDecayAlt.P.move_vector_identity
theorem qx_moveCov : Formalism.FourierDecayAlt.Q.MoveCov := Formalism.FourierDecayAlt.P.move_covariance
theorem qx_rTTSandwich : Formalism.FourierDecayAlt.Q.RTTSandwich := Formalism.FourierDecayAlt.P.rtt_sandwich
theorem qx_glevImage : Formalism.FourierDecayAlt.Q.GlevImage := Formalism.FourierDecayAlt.P.level_group_image
theorem qx_levelTransfer : Formalism.FourierDecayAlt.Q.LevelTransfer := Formalism.FourierDecayAlt.P.level_transfer
theorem qx_ruleLeft : Formalism.FourierDecayAlt.Q.RuleLeft := Formalism.FourierDecayAlt.P.left_action_rule
theorem qx_ruleTorus : Formalism.FourierDecayAlt.Q.RuleTorus := Formalism.FourierDecayAlt.P.torus_action_rule
theorem qx_tInvariant : Formalism.FourierDecayAlt.Q.TInvariant := Formalism.FourierDecayAlt.P.operator_invariance
theorem qx_tPreservesFF : Formalism.FourierDecayAlt.Q.TPreservesFF := Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms
theorem qx_capCommute : Formalism.FourierDecayAlt.Q.CapCommute := Formalism.FourierDecayAlt.P.capelli_commutation
theorem qx_hermHaar : Formalism.FourierDecayAlt.Q.HermHaar := Formalism.FourierDecayAlt.P.hermitian_haar_invariance
theorem qx_hermFromSteps : Formalism.FourierDecayAlt.Q.HermFromSteps := Formalism.FourierDecayAlt.P.hermitian_from_algebra
theorem qx_wCellBigCell : Formalism.FourierDecayAlt.Q.WCellBigCell := Formalism.FourierDecayAlt.P.weyl_cell_big_cell
theorem ux_composeDD : Formalism.FourierDecayAlt.U.ComposeDD := Formalism.FourierDecayAlt.P.compose_discrete_series
theorem unipotent_first_corollary_plain : Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator := Formalism.FourierDecayAlt.P.corollary_u1_plain
theorem corollary_u1_truncated : Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt
theorem unipotent_cost_bound_of_parts : Formalism.FourierDecayAlt.U.DerivativeCostFromComponents := Formalism.FourierDecayAlt.P.derivative_cost_of_parts
theorem chainSum_true : Formalism.FourierDecayAlt.crystallineComparison.ChainSum := Formalism.FourierDecayAlt.P.chain_sum_identity
theorem rowSums_true : Formalism.FourierDecayAlt.crystallineComparison.RowSums := Formalism.FourierDecayAlt.P.row_sums_identity
theorem product_of_sizes_bound : Formalism.FourierDecayAlt.crystallineComparison.SizesProduct := Formalism.FourierDecayAlt.P.sizes_product_identity
theorem base_gram_monotone : Formalism.FourierDecayAlt.crystallineComparison.BaseGramMonotone := Formalism.FourierDecayAlt.P.baseGramMonotone
theorem corollary_t : Formalism.FourierDecayAlt.crystallineComparison.CorT := Formalism.FourierDecayAlt.P.cosetSumBound
theorem block_estimate_of_sum_form : Formalism.FourierDecayAlt.crystallineComparison.EstBlockOfSumForm := Formalism.FourierDecayAlt.P.blockEstimateOfCosetSum
theorem mean_bound : Formalism.FourierDecayAlt.crystallineComparison.MeanBound := Formalism.FourierDecayAlt.P.mean_bound_estimate
theorem meanSplit_crystalline_true : Formalism.FourierDecayAlt.crystallineComparison.MeanSplit := Formalism.FourierDecayAlt.P.mean_split_identity
theorem qx_rightTypeAction : Formalism.FourierDecayAlt.Q.RightTypeAction := Formalism.FourierDecayAlt.P.right_type_action
theorem qx_leftTypeAction : Formalism.FourierDecayAlt.Q.LeftTypeAction := Formalism.FourierDecayAlt.P.left_type_action
theorem sliceCoordinateSizes_true : Formalism.FourierDecayAlt.U.SliceCoordinateSizes := Formalism.FourierDecayAlt.P.coordinate_sizes_in_norm
theorem unipotent_size_bound_second : Formalism.FourierDecayAlt.U.CoordinateDecay := Formalism.FourierDecayAlt.P.norm_decay_in_coordinates
theorem pointwiseIntegralBound_true : Formalism.FourierDecayAlt.U.PointwiseIntegralBound := Formalism.FourierDecayAlt.P.phi_pointwise_bound
theorem ux_theoremU : Formalism.FourierDecayAlt.U.TheoremU := Formalism.FourierDecayAlt.P.theorem_u
theorem ux_phiSuppG : Formalism.FourierDecayAlt.U.PhiSuppG := Formalism.FourierDecayAlt.P.phi_support_level_function
theorem corollary_u2 : Formalism.FourierDecayAlt.U.GermExpansionHypothesis := Formalism.FourierDecayAlt.P.corollary_u2_germ_hypothesis
theorem ux_useDerivBound : Formalism.FourierDecayAlt.U.UseDerivBound := Formalism.FourierDecayAlt.P.derivative_bound_in_banach_space
theorem ux_useGerm : Formalism.FourierDecayAlt.U.UseGerm := Formalism.FourierDecayAlt.P.germ_expansion_applies
theorem ux_useGermTop : Formalism.FourierDecayAlt.U.UseGermTop := Formalism.FourierDecayAlt.P.germ_expansion_top_level
theorem ux_useGermTopCount : Formalism.FourierDecayAlt.U.UseGermTopCount := Formalism.FourierDecayAlt.P.germ_expansion_top_count
theorem ux_germInForm : Formalism.FourierDecayAlt.U.GermInForm := Formalism.FourierDecayAlt.P.germ_expansion_in_form_space
theorem majorant_integral_finite : Formalism.FourierDecayAlt.crystallineComparison.MajIntegral := Formalism.FourierDecayAlt.P.majorantIntegral
theorem majorant_integral_product_form : Formalism.FourierDecayAlt.crystallineComparison.MajIntegralProd := Formalism.FourierDecayAlt.P.majorantIntegralProd
theorem latticeHerglotzBound_true : Formalism.FourierDecayAlt.crystallineComparison.LatticeHerglotzBound := Formalism.FourierDecayAlt.P.latticeHerglotzBound_statement
theorem qx_detHat : Formalism.FourierDecayAlt.Q.DetHat := Formalism.FourierDecayAlt.P.determinant_hat
theorem qx_detHatRegular : Formalism.FourierDecayAlt.Q.DetHatRegular := Formalism.FourierDecayAlt.P.determinant_hat_regular
theorem qx_regularToSmooth : Formalism.FourierDecayAlt.Q.RegularToSmooth := Formalism.FourierDecayAlt.P.regular_to_smooth
theorem qx_detGeneric : Formalism.FourierDecayAlt.Q.DetGeneric := Formalism.FourierDecayAlt.P.determinant_generic
theorem lattice_sum_summable : Formalism.FourierDecayAlt.crystallineComparison.LatticeSummable := Formalism.FourierDecayAlt.P.latticeSummable_statement
theorem mean_value_exists : Formalism.FourierDecayAlt.crystallineComparison.MeanExists := Formalism.FourierDecayAlt.P.invariantMeanExists
theorem pairingGramBound_true : Formalism.FourierDecayAlt.PairingProductCorollary.PairingGramBound := Formalism.FourierDecayAlt.P.second_polynomial_first_identity
theorem unnormalisedLiftBound_of_components : Formalism.FourierDecayAlt.PairingProductCorollary.UnnormalisedLiftBoundFromComponents := Formalism.FourierDecayAlt.P.unipotent_degree_three_of_clauses
theorem lower_block_normalised_bound_of_components : Formalism.FourierDecayAlt.PairingProductCorollary.LowerBlockNormalisedBoundFromComponents := Formalism.FourierDecayAlt.P.second_polynomial_third_of_parts
theorem theorem_p2 : Formalism.FourierDecayAlt.PairingProductCorollary.LowerBlockLiftBound := Formalism.FourierDecayAlt.P.lower_block_lift_bound
theorem theorem_p2_of_parts : Formalism.FourierDecayAlt.PairingProductCorollary.LowerBlockLiftBoundFromComponents := Formalism.FourierDecayAlt.P.lower_block_lift_bound_of_components
theorem third_period_bound_part_a_of_parts : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockRecursiveBoundFromComponents := Formalism.FourierDecayAlt.P.leading_block_recursive_bound_of_components
theorem third_period_part_b_from_part_a : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockBoundFromRecursion := Formalism.FourierDecayAlt.P.third_polynomial_second_of_first
theorem third_period_theorem : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockLiftBound := Formalism.FourierDecayAlt.P.leading_block_lift_bound
theorem third_period_theorem_of_parts : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockLiftBoundFromComponents := Formalism.FourierDecayAlt.P.leading_block_lift_bound_of_components
theorem places_combine : Formalism.FourierDecayAlt.PairingProductCorollary.PlacesCombine := Formalism.FourierDecayAlt.P.local_places_combine
theorem third_period_prime_combination : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockSeveralPlacesBound := Formalism.FourierDecayAlt.P.third_polynomial_prime_combine
theorem factors_positive : Formalism.FourierDecayAlt.PairingProductCorollary.FactorsPositive := Formalism.FourierDecayAlt.P.local_factors_positive
theorem truncation_room : Formalism.FourierDecayAlt.PairingProductCorollary.CutRoom := Formalism.FourierDecayAlt.P.truncation_room_estimate
theorem weight_function_lower_bound : Formalism.FourierDecayAlt.PairingProductCorollary.WeightLower := Formalism.FourierDecayAlt.P.weight_lower_bound
theorem corollary_a_product : Formalism.FourierDecayAlt.PairingProductCorollary.CorAProduct := Formalism.FourierDecayAlt.P.constant_product_corollary
theorem corollary_a_constant_wave : Formalism.FourierDecayAlt.PairingProductCorollary.CorAConstWave := Formalism.FourierDecayAlt.P.constant_wave_corollary
theorem constant_term_top_weight : Formalism.FourierDecayAlt.PairingProductCorollary.CorAConstTop := Formalism.FourierDecayAlt.P.constant_top_corollary
theorem weighted_kernel_positive_semidefinite : Formalism.FourierDecayAlt.PairingProductCorollary.WeightedKernelPSD := Formalism.FourierDecayAlt.P.weighted_kernel_posSemidef
theorem scale_thresholds : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleThresholds := Formalism.FourierDecayAlt.P.scale_thresholds_estimate
theorem scale_thresholds_below : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleThresholdsBelow := Formalism.FourierDecayAlt.P.pairing_product_scale_bounds_below
theorem scale_beta : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleBeta := Formalism.FourierDecayAlt.P.scaling_beta_identity
theorem scaling_character_identity : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleCharacter := Formalism.FourierDecayAlt.P.scale_character_identity
theorem standard_frame_phase : Formalism.FourierDecayAlt.PairingProductCorollary.StdFramePhase := Formalism.FourierDecayAlt.P.standard_frame_phase_alt
theorem block_phase : Formalism.FourierDecayAlt.PairingProductCorollary.BlockPhase := Formalism.FourierDecayAlt.P.block_phase_identity
theorem real_character : Formalism.FourierDecayAlt.PairingProductCorollary.RealCharacter := Formalism.FourierDecayAlt.P.real_character_identity
theorem real_frame_entry : Formalism.FourierDecayAlt.PairingProductCorollary.RealFrameEntry := Formalism.FourierDecayAlt.P.real_frame_entry_alt
theorem frame_map_jacobian : Formalism.FourierDecayAlt.PairingProductCorollary.FrameJacobian := Formalism.FourierDecayAlt.P.frame_jacobian_formula
theorem ga_exponent : Formalism.FourierDecayAlt.PairingProductCorollary.GaExponent := Formalism.FourierDecayAlt.P.gamma_exponent_formula
theorem frame_integral_formula : Formalism.FourierDecayAlt.PairingProductCorollary.FrameIntegral := Formalism.FourierDecayAlt.P.frame_integral_formula_alt
theorem cofactor_pair_identity : Formalism.FourierDecayAlt.C7.CofactorPair := Formalism.FourierDecayAlt.P.cofactorPair_statement
theorem cofactor_corner : Formalism.FourierDecayAlt.C7.CofactorCorner := Formalism.FourierDecayAlt.P.cofactor_corner_identity
theorem adjugate_last_column : Formalism.FourierDecayAlt.C7.AdjLastCol := Formalism.FourierDecayAlt.P.adjLastCol_statement
theorem gram_determinant_cofactor_expansion : Formalism.FourierDecayAlt.C7.GramCofactor := Formalism.FourierDecayAlt.P.gram_cofactor_identity
theorem omega_norm_cofactor_formula : Formalism.FourierDecayAlt.C7.OmNorm := Formalism.FourierDecayAlt.P.omega_norm_identity
theorem omega_norm_cofactor : Formalism.FourierDecayAlt.C7.OmNormCofactor := Formalism.FourierDecayAlt.P.omNormCofactor_statement
theorem omega_norm_cofactor_of_parts : Formalism.FourierDecayAlt.C7.OmNormCofactorOfParts := Formalism.FourierDecayAlt.P.omNormCofactorOfParts_statement
theorem scalar_pair_common : Formalism.FourierDecayAlt.C7.ScalarPairCommon := Formalism.FourierDecayAlt.P.scalar_pair_common_factor
theorem torus_action_group_structure : Formalism.FourierDecayAlt.C7.TaGroup := Formalism.FourierDecayAlt.P.torus_action_group
theorem ta_argument_multiplicative : Formalism.FourierDecayAlt.C7.TaArgMul := Formalism.FourierDecayAlt.P.torus_argument_multiplicative
theorem schur_product_positive_semidefinite : Formalism.FourierDecayAlt.C7.SchurProductPSD := Formalism.FourierDecayAlt.P.schur_product_posSemidef
theorem form_monotone : Formalism.FourierDecayAlt.C7.FormMono := Formalism.FourierDecayAlt.P.c7_form_mono
theorem form_monotone_of_schur : Formalism.FourierDecayAlt.C7.FormMonoOfSchur := Formalism.FourierDecayAlt.P.c7_form_mono_of_schur
theorem extend_zero_psd : Formalism.FourierDecayAlt.C7.ExtendZeroPSD := Formalism.FourierDecayAlt.P.extend_by_zero_posSemidef
theorem schur_isotypic : Formalism.FourierDecayAlt.C7.SchurIsotypic := Formalism.FourierDecayAlt.P.schur_isotypic_decomposition
theorem det_w : Formalism.FourierDecayAlt.C7.DetW := Formalism.FourierDecayAlt.P.weight_determinant
theorem d_equal_roots : Formalism.FourierDecayAlt.C7.DEqualRoots := Formalism.FourierDecayAlt.P.equal_roots_determinant
theorem d_equal_of_parts : Formalism.FourierDecayAlt.C7.DEqualOfParts := Formalism.FourierDecayAlt.P.equal_roots_of_parts
theorem n_prime_le : Formalism.FourierDecayAlt.C7.NprimeLe := Formalism.FourierDecayAlt.P.nprime_le_bound
theorem threshold_e : Formalism.FourierDecayAlt.C7.ThresholdE := Formalism.FourierDecayAlt.P.threshold_exponent_estimate
theorem degree_count_of_eigenvalues : Formalism.FourierDecayAlt.C7.DegreeCount := Formalism.FourierDecayAlt.P.degree_count_identity
theorem budget_sum : Formalism.FourierDecayAlt.C7.BudgetSum := Formalism.FourierDecayAlt.P.budget_sum_estimate
theorem lemma_b3_count : Formalism.FourierDecayAlt.C7.LetterProductDegreeCount := Formalism.FourierDecayAlt.P.c7_letter_product_degree_count
theorem eigen_shift : Formalism.FourierDecayAlt.C7.EigenShift := Formalism.FourierDecayAlt.P.eigenvalue_shift
theorem lambda_side : Formalism.FourierDecayAlt.C7.LamSide := Formalism.FourierDecayAlt.P.lambda_side_inequality
theorem rho_side_identity : Formalism.FourierDecayAlt.C7.RhoSide := Formalism.FourierDecayAlt.P.rho_side_inequality
theorem sign_count : Formalism.FourierDecayAlt.C7.SignCount := Formalism.FourierDecayAlt.P.sign_change_count
theorem p_sign : Formalism.FourierDecayAlt.C7.PSign := Formalism.FourierDecayAlt.P.polynomial_sign
theorem p_sign_of_parts : Formalism.FourierDecayAlt.C7.PSignOfParts := Formalism.FourierDecayAlt.P.polynomial_sign_of_parts
theorem roots_out_joint : Formalism.FourierDecayAlt.C7.RootsOutJoint := Formalism.FourierDecayAlt.P.roots_outside_jointly
theorem roots_outside_disc_of_parts : Formalism.FourierDecayAlt.C7.RootsOutOfParts := Formalism.FourierDecayAlt.P.roots_outside_of_parts
theorem lemma_e_interlacing_of_parts : Formalism.FourierDecayAlt.C7.LemmaEInterlacingOfParts := Formalism.FourierDecayAlt.P.interlacing_of_parts
theorem qx_expRowsFromRowForm : Formalism.FourierDecayAlt.Q.ExpRowsFromRowForm := Formalism.FourierDecayAlt.P.line_expansions_from_line_form
theorem qx_borderFromExpansions : Formalism.FourierDecayAlt.Q.BorderFromExpansions := Formalism.FourierDecayAlt.P.border_from_expansions
theorem qx_chainFromStep : Formalism.FourierDecayAlt.Q.ChainFromStep := Formalism.FourierDecayAlt.P.chain_recursion_from_single_descent
theorem qx_detCoreFromSteps : Formalism.FourierDecayAlt.Q.DetCoreFromSteps := Formalism.FourierDecayAlt.P.determinant_capelli_from_descent
theorem qx_detLevelFromCore : Formalism.FourierDecayAlt.Q.DetLevelFromCore := Formalism.FourierDecayAlt.P.determinant_level_from_capelli_identity
theorem qx_eigenBesselFromCommutes : Formalism.FourierDecayAlt.Q.EigenBesselFromCommutes := Formalism.FourierDecayAlt.P.eigen_bessel_from_commuting_operators
theorem qx_radOps : Formalism.FourierDecayAlt.Q.RadOps := Formalism.FourierDecayAlt.P.radial_operators
theorem qx_actualOpsFromSteps : Formalism.FourierDecayAlt.Q.ActualOpsFromSteps := Formalism.FourierDecayAlt.P.actual_operators_from_parts
theorem qx_actualAdjointFromHerm : Formalism.FourierDecayAlt.Q.ActualAdjointFromHerm := Formalism.FourierDecayAlt.P.actual_adjointness_from_hermitian
theorem qx_levelStartFromNormalForm : Formalism.FourierDecayAlt.Q.LevelStartFromNormalForm := Formalism.FourierDecayAlt.P.level_start_from_normal_form
theorem qx_actualStartFromLevels : Formalism.FourierDecayAlt.Q.ActualStartFromLevels := Formalism.FourierDecayAlt.P.actual_start_from_level_starts
theorem w_inverse : Formalism.FourierDecayAlt.C7.WInv := Formalism.FourierDecayAlt.P.weight_inverse
theorem w_exact : Formalism.FourierDecayAlt.C7.WExact := Formalism.FourierDecayAlt.P.weight_exactness
theorem nf_weight : Formalism.FourierDecayAlt.C7.NFWeight := Formalism.FourierDecayAlt.P.normal_form_weight
theorem dbar_conjugate_w : Formalism.FourierDecayAlt.C7.DbarConjW := Formalism.FourierDecayAlt.P.dbar_conjugation_weight
theorem leibniz_rule_lower_diagonal : Formalism.FourierDecayAlt.C7.LdLeibniz := Formalism.FourierDecayAlt.P.leibniz_log_derivative
theorem density_change_of_variables : Formalism.FourierDecayAlt.crystallineComparison.DensityChange := Formalism.FourierDecayAlt.P.rootPushforwardDensity
theorem eigenvalueInterlacing_true : Formalism.FourierDecayAlt.C7.LemmaEInterlacing := Formalism.FourierDecayAlt.P.eigenvalue_interlacing
theorem hilbert_schmidt_frame : Formalism.FourierDecayAlt.C7.HSFrame := Formalism.FourierDecayAlt.P.hilbertSchmidt_frame
theorem fibre_chain_exponent : Formalism.FourierDecayAlt.C6.FibChainExp := Formalism.FourierDecayAlt.P.fibre_chain_expansion
theorem fibre_exponent_formula : Formalism.FourierDecayAlt.C6.FibExpText := Formalism.FourierDecayAlt.P.fibre_expansion_identity
theorem fibre_exponent_zero_fails : Formalism.FourierDecayAlt.C6.FibExpZeroFails := Formalism.FourierDecayAlt.P.fibre_expansion_zero_fails
theorem homogeneity_natural : Formalism.FourierDecayAlt.C6.SSNatHomog := Formalism.FourierDecayAlt.P.homogeneity_natural_degree
theorem d_min_polynomial : Formalism.FourierDecayAlt.C6.DminPoly := Formalism.FourierDecayAlt.P.minor_polynomial_property
theorem gf_polynomial : Formalism.FourierDecayAlt.C6.GfPoly := Formalism.FourierDecayAlt.P.gram_function_polynomial
theorem gf_d_last : Formalism.FourierDecayAlt.C6.GfDlast := Formalism.FourierDecayAlt.P.gram_function_last_minor
theorem budget_arithmetic : Formalism.FourierDecayAlt.C6.BudgetArith := Formalism.FourierDecayAlt.P.c6_budgetArith_proof
theorem bigCellVanishingThreshold_true : Formalism.FourierDecayAlt.C6.BigCellVanishingThreshold := Formalism.FourierDecayAlt.P.big_cell_threshold
theorem density_threshold_j : Formalism.FourierDecayAlt.C6.DensThreshJ := Formalism.FourierDecayAlt.P.inner_density_threshold
theorem density_threshold_top : Formalism.FourierDecayAlt.C6.DensThreshTop := Formalism.FourierDecayAlt.P.top_density_threshold
theorem big_cell_vanishing_of_commute : Formalism.FourierDecayAlt.C6.BigCellVanishingOfCommute := Formalism.FourierDecayAlt.P.big_cell_vanishing_of_commute'
theorem averaging_zero : Formalism.FourierDecayAlt.C6.AveragingZero := Formalism.FourierDecayAlt.P.averaging_vanishes
theorem averaging_identity_of_parts : Formalism.FourierDecayAlt.C6.AveragingOfParts := Formalism.FourierDecayAlt.P.averaging_of_parts
theorem rootFacts_true : Formalism.FourierDecayAlt.C6.RootFacts := Formalism.FourierDecayAlt.P.polynomial_root_facts
theorem vanishing_of_parts : Formalism.FourierDecayAlt.C6.VanishingOfParts := Formalism.FourierDecayAlt.P.vanishing_of_components_true
theorem scale_threshold_at_one : Formalism.FourierDecayAlt.PairingProductCorollary.ScaleThresholdsOne := Formalism.FourierDecayAlt.P.scale_thresholds_at_one
theorem pair_adjoint : Formalism.FourierDecayAlt.FormPairingAction.PairAdj := Formalism.FourierDecayAlt.P.pairing_adjoint_identity
theorem cs_positive : Formalism.FourierDecayAlt.FormPairingAction.CSPos := Formalism.FourierDecayAlt.P.cauchy_schwarz_positive
theorem sesquilinear_form_properties : Formalism.FourierDecayAlt.FormPairingAction.FormSesq := Formalism.FourierDecayAlt.P.form_sesquilinear
theorem form_pairing_gram_sum : Formalism.FourierDecayAlt.FormPairingAction.GramSum := Formalism.FourierDecayAlt.P.gram_sum_identity
theorem gram_positive : Formalism.FourierDecayAlt.FormPairingAction.GramPos := Formalism.FourierDecayAlt.P.gram_matrix_positive
theorem gram_realisation : Formalism.FourierDecayAlt.FormPairingAction.GramRealise := Formalism.FourierDecayAlt.P.gram_matrix_realisation
theorem dualityPairingFormula_true : Formalism.FourierDecayAlt.FormPairingAction.DualityPairingFormula := Formalism.FourierDecayAlt.P.duality_pairing_formula
theorem derivative_lemma_part_b : Formalism.FourierDecayAlt.FormPairingAction.DualityIsometry := Formalism.FourierDecayAlt.P.duality_isometry
theorem dualityCauchySchwarz_true : Formalism.FourierDecayAlt.FormPairingAction.DualityCauchySchwarz := Formalism.FourierDecayAlt.P.duality_cauchy_schwarz
theorem letterDuality_true : Formalism.FourierDecayAlt.FormPairingAction.LetterDuality := Formalism.FourierDecayAlt.P.letter_duality
theorem derivative_lemma_first_of_parts : Formalism.FourierDecayAlt.FormPairingAction.LetterDualityOfParts := Formalism.FourierDecayAlt.P.letter_duality_of_components
theorem dualKernel_true : Formalism.FourierDecayAlt.FormPairingAction.LemmaDK := Formalism.FourierDecayAlt.P.formPairingAction_dual_kernel
theorem dk_first_stage : Formalism.FourierDecayAlt.FormPairingAction.DKStep1 := Formalism.FourierDecayAlt.P.first_reduction_estimate
theorem dual_kernel_compatibility : Formalism.FourierDecayAlt.FormPairingAction.DKDualOK := Formalism.FourierDecayAlt.P.dual_kernel_duality
theorem dk_fourth_stage : Formalism.FourierDecayAlt.FormPairingAction.DKStep4 := Formalism.FourierDecayAlt.P.fourth_reduction_estimate
theorem lemma_dk_of_parts : Formalism.FourierDecayAlt.FormPairingAction.LemmaDKOfParts := Formalism.FourierDecayAlt.P.dual_kernel_lemma_of_parts
theorem grid_spacing : Formalism.FourierDecayAlt.FormPairingAction.GridSpacing := Formalism.FourierDecayAlt.P.grid_spacing_estimate
theorem logarithm_small_argument_bound : Formalism.FourierDecayAlt.FormPairingAction.LogSmall := Formalism.FourierDecayAlt.P.logarithm_small_estimate
theorem q_product : Formalism.FourierDecayAlt.FormPairingAction.QProduct := Formalism.FourierDecayAlt.P.Q_product_identity
theorem formPairingQuadratic_true : Formalism.FourierDecayAlt.FormPairingAction.LemmaQ := Formalism.FourierDecayAlt.P.lemma_Q_estimate
theorem lemma_q_of_parts : Formalism.FourierDecayAlt.FormPairingAction.LemmaQOfParts := Formalism.FourierDecayAlt.P.lemma_Q_of_parts
theorem q_w_of_real : Formalism.FourierDecayAlt.FormPairingAction.QwOfReal := Formalism.FourierDecayAlt.P.weighted_quadratic_of_real
theorem cauchySchwarzInvariantForm_true : Formalism.FourierDecayAlt.FormPairingAction.CauchySchwarzInvariantForm := Formalism.FourierDecayAlt.P.first_polynomial_bound
theorem plane_wave_norm_bound : Formalism.FourierDecayAlt.FormPairingAction.PlaneWaveNormBound := Formalism.FourierDecayAlt.P.plane_wave_norm_bound'
theorem admissible_dual_kernel : Formalism.FourierDecayAlt.FormPairingAction.AdmDK := Formalism.FourierDecayAlt.P.admDK_statement
theorem admissiblePointSizeBound_true : Formalism.FourierDecayAlt.FormPairingAction.AdmissiblePointSizeBound := Formalism.FourierDecayAlt.P.admissible_point_size_bound
theorem planeWaveNormBound_of_components : Formalism.FourierDecayAlt.FormPairingAction.PlaneWaveNormBoundOfParts := Formalism.FourierDecayAlt.P.first_polynomial_bound_of_parts
theorem sizeBound_of_components : Formalism.FourierDecayAlt.FormPairingAction.SizeBoundOfParts := Formalism.FourierDecayAlt.P.first_polynomial_size_of_clauses
theorem capelliIdentityEntry_true : Formalism.FourierDecayAlt.Q.CapelliIdentityEntry := Formalism.FourierDecayAlt.P.capelli_two_by_two
theorem qx_zetaComm : Formalism.FourierDecayAlt.Q.ZetaComm := Formalism.FourierDecayAlt.P.zeta_commutes
theorem radialDecomposition_of_components : Formalism.FourierDecayAlt.Q.RadialDecompositionOfParts := Formalism.FourierDecayAlt.P.q_radial_decomposition_of_pieces
theorem jf_cVLeft : Formalism.FourierDecayAlt.JF.CVLeft := Formalism.FourierDecayAlt.P.capelli_left_translation
theorem jf_cVPost : Formalism.FourierDecayAlt.JF.CVPost := Formalism.FourierDecayAlt.P.capelli_post_composition
theorem jf_cVRhoOfParts : Formalism.FourierDecayAlt.JF.CVRhoOfParts := Formalism.FourierDecayAlt.P.capelli_rho_of_parts
theorem jf_cVWordSum : Formalism.FourierDecayAlt.JF.CVWordSum := Formalism.FourierDecayAlt.P.capelli_word_sum
theorem jf_cVUnderIntOfParts : Formalism.FourierDecayAlt.JF.CVUnderIntOfParts := Formalism.FourierDecayAlt.P.capelli_under_integral_of_parts
theorem jf_besselCommutesOfParts : Formalism.FourierDecayAlt.JF.BesselCommutesOfParts := Formalism.FourierDecayAlt.P.bessel_capelli_commute_of_parts
theorem jf_jThetaOfParts : Formalism.FourierDecayAlt.JF.JThetaOfParts := Formalism.FourierDecayAlt.P.theta_bessel_commute_of_parts
theorem radialComponentIntertwines_of_components : Formalism.FourierDecayAlt.JF.RadialPartIntertwinesFromComponents := Formalism.FourierDecayAlt.P.radial_part_intertwines_of_parts
theorem jf_psiQUnique : Formalism.FourierDecayAlt.JF.PsiQUnique := Formalism.FourierDecayAlt.P.psiQUnique_true
theorem jf_equivDetOfOnto : Formalism.FourierDecayAlt.JF.EquivDetOfOnto := Formalism.FourierDecayAlt.P.equiv_det_of_onto
theorem jf_thetaEquiv : Formalism.FourierDecayAlt.JF.ThetaEquiv := Formalism.FourierDecayAlt.P.theta_equivariant
theorem jf_jqSmoothOfParts : Formalism.FourierDecayAlt.JF.JqSmoothOfParts := Formalism.FourierDecayAlt.P.bessel_smooth_of_parts
theorem jf_jWordsOfDom : Formalism.FourierDecayAlt.JF.JWordsOfDom := Formalism.FourierDecayAlt.P.bessel_words_of_domain
theorem jf_rwRho : Formalism.FourierDecayAlt.JF.RwRho := Formalism.FourierDecayAlt.P.rewrite_rho_action
theorem jf_gqDom : Formalism.FourierDecayAlt.JF.GqDom := Formalism.FourierDecayAlt.P.big_cell_domain
theorem jf_gqOm : Formalism.FourierDecayAlt.JF.GqOm := Formalism.FourierDecayAlt.P.big_cell_orbit_set
theorem radialDecomposition_of_components_q : Formalism.FourierDecayAlt.Q.RadialDecompositionOfParts := Formalism.FourierDecayAlt.P.t22_entry_from_descent_identities
theorem c_gramPSDOfParts : Formalism.FourierDecayAlt.C.GramPSDOfParts := Formalism.FourierDecayAlt.P.gram_positive_semidefinite
theorem c_wordsPosOfParts : Formalism.FourierDecayAlt.C.WordsPosOfParts := Formalism.FourierDecayAlt.P.words_pos_of_parts
theorem c_estWaveOfParts : Formalism.FourierDecayAlt.C.EstWaveOfParts := Formalism.FourierDecayAlt.P.wave_estimate_of_integral
theorem c_poissonInputOfParts : Formalism.FourierDecayAlt.C.PoissonInputOfParts := Formalism.FourierDecayAlt.P.poisson_input_of_parts
theorem c_estLiftOfParts : Formalism.FourierDecayAlt.C.EstLiftOfParts := Formalism.FourierDecayAlt.P.lift_estimate_of_base
theorem c_estBlockOfParts : Formalism.FourierDecayAlt.C.EstBlockOfParts := Formalism.FourierDecayAlt.P.block_estimate_of_base
theorem c_estEOfParts : Formalism.FourierDecayAlt.C.EstEOfParts := Formalism.FourierDecayAlt.P.level_zero_estimate_product
theorem c_cutoffOfParts : Formalism.FourierDecayAlt.C.CutoffOfParts := Formalism.FourierDecayAlt.P.cutoff_of_parts
theorem c_realInputsConcrete : Formalism.FourierDecayAlt.C.RealInputsConcrete := Formalism.FourierDecayAlt.P.real_inputs_concrete_holds
theorem c_realInputsConcreteOfParts : Formalism.FourierDecayAlt.C.RealInputsConcreteOfParts := Formalism.FourierDecayAlt.P.real_inputs_by_parts
theorem c_theoremAConcrete : Formalism.FourierDecayAlt.C.TheoremAConcrete := Formalism.FourierDecayAlt.P.concrete_bound_holds
theorem c_theoremAConcreteOfParts : Formalism.FourierDecayAlt.C.TheoremAConcreteOfParts := Formalism.FourierDecayAlt.P.concrete_bound_of_recursion
theorem u_map_frame : Formalism.FourierDecayAlt.C2.UMapFrame := Formalism.FourierDecayAlt.P.unipotent_map_frame
theorem z_hat_equivalence : Formalism.FourierDecayAlt.C2.ZhatEquiv := Formalism.FourierDecayAlt.P.zhat_equivalence
theorem det_nonzero : Formalism.FourierDecayAlt.C2.DetNonzero := Formalism.FourierDecayAlt.P.determinant_nonzero
theorem relevant_orbit_fourth_case : Formalism.FourierDecayAlt.C2.C1iv := Formalism.FourierDecayAlt.P.stabilizer_fourth_condition
theorem relevant_pair : Formalism.FourierDecayAlt.C2.RelevantPair := Formalism.FourierDecayAlt.P.relevant_pair_criterion
theorem trivial_relevant_orbit_contribution : Formalism.FourierDecayAlt.C2.RelevantTriv := Formalism.FourierDecayAlt.P.relevant_trivial_case
theorem relevant_critical : Formalism.FourierDecayAlt.C2.RelevantCrit := Formalism.FourierDecayAlt.P.relevant_criterion
theorem inverse_star_subgroup : Formalism.FourierDecayAlt.C2.InvStarSub := Formalism.FourierDecayAlt.P.inverse_star_substitution
theorem negation_conjugation_symmetry : Formalism.FourierDecayAlt.C2.PsiNegConj := Formalism.FourierDecayAlt.P.psi_neg_conj_identity
theorem stabiliser_antidiagonal : Formalism.FourierDecayAlt.C2.StabAntidiag := Formalism.FourierDecayAlt.P.stabilizer_antidiagonal
theorem relevant_orbit_monotone : Formalism.FourierDecayAlt.C2.RelevantMono := Formalism.FourierDecayAlt.P.relevant_monotone
theorem relevant_monotone_of_parts : Formalism.FourierDecayAlt.C2.RelevantMonoOfParts := Formalism.FourierDecayAlt.P.relevant_monotone_of_parts_alt
theorem lp_coordinates : Formalism.FourierDecayAlt.C2.LPCoords := Formalism.FourierDecayAlt.P.lower_parabolic_coordinates
theorem u_r_image : Formalism.FourierDecayAlt.C2.URImage := Formalism.FourierDecayAlt.P.unipotent_radical_image
theorem upper_split_of_lower : Formalism.FourierDecayAlt.C2.UpSplitOfLowSplit := Formalism.FourierDecayAlt.P.upper_splitting_of_lower
theorem minor_c_nonzero : Formalism.FourierDecayAlt.C2.MinorCNonzero := Formalism.FourierDecayAlt.P.minor_C_nonzero
theorem projection_onto_relevant_part : Formalism.FourierDecayAlt.C2.ProjClaim := Formalism.FourierDecayAlt.P.projection_property
theorem threshold_exponent_comparison : Formalism.FourierDecayAlt.C2.SliceThresholdBound := Formalism.FourierDecayAlt.P.slice_threshold_bound
theorem c2_gram_product_identity : Formalism.FourierDecayAlt.C2.GramProductIdentity := Formalism.FourierDecayAlt.P.gram_product_identity
theorem weight_four_exponent : Formalism.FourierDecayAlt.C2.SliceExponentIdentity := Formalism.FourierDecayAlt.P.slice_exponent_identity
theorem stabiliser_block : Formalism.FourierDecayAlt.C2.StabBlock := Formalism.FourierDecayAlt.P.stabilizer_block_form
theorem stabiliser_antidiagonal_exact : Formalism.FourierDecayAlt.C2.StabAntidiagExact := Formalism.FourierDecayAlt.P.stabilizer_antidiagonal_exact
theorem slotExpansionLeadingCoefficients_true : Formalism.FourierDecayAlt.FormPairingAction.PositionExpansionTopCoefficients := Formalism.FourierDecayAlt.P.first_polynomial_expansion_identity
theorem first_period_polynomial_degree : Formalism.FourierDecayAlt.FormPairingAction.GridDegreeIdentity := Formalism.FourierDecayAlt.P.first_polynomial_degree_identity
theorem combinedDegreeSizeBound_true : Formalism.FourierDecayAlt.FormPairingAction.CombinedDegreeSizeBound := Formalism.FourierDecayAlt.P.unipotent_degree_bound
theorem first_period_degree_of_parts : Formalism.FourierDecayAlt.FormPairingAction.DegreeIdentityOfParts := Formalism.FourierDecayAlt.P.first_polynomial_degree_of_clauses
theorem combinedBound_of_degreeSize : Formalism.FourierDecayAlt.FormPairingAction.CombinedBoundOfDegreeSize := Formalism.FourierDecayAlt.P.unipotent_degree_of_clauses
theorem qx_branching : Formalism.FourierDecayAlt.Q.Branching := Formalism.FourierDecayAlt.P.branching_proof
theorem radialDecompositionSpectral_true : Formalism.FourierDecayAlt.Q.RadialDecompositionSpectral := Formalism.FourierDecayAlt.P.spectral_two_by_two
theorem first_period_bound_part_c : Formalism.FourierDecayAlt.FormPairingAction.NormaliserLowerBound := Formalism.FourierDecayAlt.P.first_polynomial_third_clause
theorem first_period_corollary : Formalism.FourierDecayAlt.FormPairingAction.SmallParameterNormBound := Formalism.FourierDecayAlt.P.first_polynomial_corollary
theorem first_period_theorem : Formalism.FourierDecayAlt.FormPairingAction.PlaneWaveBoundAllPlaces := Formalism.FourierDecayAlt.P.first_polynomial_theorem
theorem first_period_bound_part_c_of_parts : Formalism.FourierDecayAlt.FormPairingAction.NormaliserBoundOfParts := Formalism.FourierDecayAlt.P.third_clause_of_parts
theorem corollary_p1_of_parts : Formalism.FourierDecayAlt.FormPairingAction.SmallParameterBoundOfParts := Formalism.FourierDecayAlt.P.corollary_of_parts
theorem theorem_p1_of_parts : Formalism.FourierDecayAlt.FormPairingAction.PlaneWaveTheoremOfParts := Formalism.FourierDecayAlt.P.first_polynomial_theorem_of_components
theorem jf_psiOnto : Formalism.FourierDecayAlt.JF.PsiOnto := Formalism.FourierDecayAlt.P.psiOnto_true
theorem jf_equivDet : Formalism.FourierDecayAlt.JF.EquivDet := Formalism.FourierDecayAlt.P.equiv_det
theorem peel_p1 : Formalism.FourierDecayAlt.C3.PeelingOmittedColumn := Formalism.FourierDecayAlt.P.first_peeling_identity
theorem peeling_second_variable : Formalism.FourierDecayAlt.C3.PeelingCovector := Formalism.FourierDecayAlt.P.second_peeling_identity
theorem peeling_third_variable : Formalism.FourierDecayAlt.C3.PeelingDualColumn := Formalism.FourierDecayAlt.P.third_peeling_identity
theorem peel_p4 : Formalism.FourierDecayAlt.C3.PeelingDualCovector := Formalism.FourierDecayAlt.P.fourth_peeling_identity
theorem antidiagonal_det : Formalism.FourierDecayAlt.C3.AntiDiagDet := Formalism.FourierDecayAlt.P.antidiagonal_determinant
theorem leading_derivative_at_zero : Formalism.FourierDecayAlt.C3.DleadZb := Formalism.FourierDecayAlt.P.derivative_leading_zb
theorem plucker_e1 : Formalism.FourierDecayAlt.C3.MinorsFirstCase := Formalism.FourierDecayAlt.P.minors_first_case
theorem plucker_e3 : Formalism.FourierDecayAlt.C3.MinorsThirdCase := Formalism.FourierDecayAlt.P.third_polynomial_expansion
theorem sign_e : Formalism.FourierDecayAlt.C3.SignE := Formalism.FourierDecayAlt.P.sign_permutation_identity
theorem first_elementary_exponent : Formalism.FourierDecayAlt.C3.ExpansionOmittedColumn := Formalism.FourierDecayAlt.P.first_expansion_identity
theorem exponent_e2 : Formalism.FourierDecayAlt.C3.ExpansionDualColumn := Formalism.FourierDecayAlt.P.second_expansion_identity
theorem exponent_e3 : Formalism.FourierDecayAlt.C3.ExpansionCovector := Formalism.FourierDecayAlt.P.column_indicator_expansion
theorem exponent_e4 : Formalism.FourierDecayAlt.C3.ExpansionDualCovector := Formalism.FourierDecayAlt.P.fourth_expansion_identity
theorem exponent_e1_of_parts : Formalism.FourierDecayAlt.C3.ExpansionFirstCaseFromComponents := Formalism.FourierDecayAlt.P.first_expansion_of_parts
theorem exponent_of_second_elementary_term : Formalism.FourierDecayAlt.C3.ExpansionSecondCaseFromComponents := Formalism.FourierDecayAlt.P.second_expansion_of_parts
theorem exponent_e3_of_parts : Formalism.FourierDecayAlt.C3.ExpansionThirdCaseFromComponents := Formalism.FourierDecayAlt.P.third_expansion_of_parts
theorem exponent_e4_of_parts : Formalism.FourierDecayAlt.C3.ExpansionFourthCaseFromComponents := Formalism.FourierDecayAlt.P.fourth_expansion_of_parts
theorem peeling_reduction_of_parts : Formalism.FourierDecayAlt.C3.PeelOfParts := Formalism.FourierDecayAlt.P.peeling_of_parts
theorem chain_x1 : Formalism.FourierDecayAlt.C3.LastColumnChain := Formalism.FourierDecayAlt.P.chain_first_identity
theorem chain_x1_of_parts : Formalism.FourierDecayAlt.C3.LastColumnChainFromComponents := Formalism.FourierDecayAlt.P.chain_first_of_parts
theorem right_derivation_rule : Formalism.FourierDecayAlt.C3.RuleRightDpsi := Formalism.FourierDecayAlt.P.right_derivative_rule_psi
theorem derivation_dpsi : Formalism.FourierDecayAlt.C3.DpsiDerivation := Formalism.FourierDecayAlt.P.dpsi_is_derivation
theorem leading_coefficient_product_identity : Formalism.FourierDecayAlt.C3.LeadAA := Formalism.FourierDecayAlt.P.leading_term_identity
theorem leading_coefficient_product_vector : Formalism.FourierDecayAlt.C3.LeadAAv := Formalism.FourierDecayAlt.P.leading_term_vector_identity
theorem xi_y_z_hat : Formalism.FourierDecayAlt.C3.XiYZhat := Formalism.FourierDecayAlt.P.xi_Y_zhat_identity
theorem operatorsCommuteTranslations_true : Formalism.FourierDecayAlt.C3.OperatorsCommuteTranslations := Formalism.FourierDecayAlt.P.operators_commute_translations'
theorem isotropicNormalFormPartial_true : Formalism.FourierDecayAlt.C3.IsotropicNormalFormPartial := Formalism.FourierDecayAlt.P.isotropicNormalFormPartial_statement
theorem isotropic_normal_form_full : Formalism.FourierDecayAlt.C3.IsotropicNormalFormFull := Formalism.FourierDecayAlt.P.isotropicNormalFormFull_statement
theorem jfx_jDom : Formalism.FourierDecayAlt.JF.JDom := Formalism.FourierDecayAlt.P.bessel_integral_domain
theorem jfx_jConv : Formalism.FourierDecayAlt.JF.JConv := Formalism.FourierDecayAlt.P.bessel_integral_converges
theorem lastLevelDiagonalSlice_true : Formalism.FourierDecayAlt.JF.LastLevelDiagonalSlice := Formalism.FourierDecayAlt.P.slice_at_last_level_diagonal
theorem qx_chainStepRaw : Formalism.FourierDecayAlt.Q.ChainStepRaw := Formalism.FourierDecayAlt.P.chain_descent_relation_raw
theorem qx_chainStep : Formalism.FourierDecayAlt.Q.ChainStep := Formalism.FourierDecayAlt.P.chain_descent_relation
theorem qx_chainAll : Formalism.FourierDecayAlt.Q.ChainAll := Formalism.FourierDecayAlt.P.chain_recursion_all_levels
theorem qx_cVv : Formalism.FourierDecayAlt.Q.CVv := Formalism.FourierDecayAlt.P.capelli_vector_valued_all_levels
theorem qx_chainStepFromRules : Formalism.FourierDecayAlt.Q.ChainStepFromRules := Formalism.FourierDecayAlt.P.chain_descent_from_rules
theorem jf_cVRight : Formalism.FourierDecayAlt.JF.CVRight := Formalism.FourierDecayAlt.P.capelli_right_invariant
theorem jf_cVRho : Formalism.FourierDecayAlt.JF.CVRho := Formalism.FourierDecayAlt.P.capelli_rho_commute
theorem jf_gqOmOfDom : Formalism.FourierDecayAlt.JF.GqOmOfDom := Formalism.FourierDecayAlt.P.big_cell_orbit_of_domain
theorem jf_jWords : Formalism.FourierDecayAlt.JF.JWords := Formalism.FourierDecayAlt.P.jacquet_derivative_formula
theorem jf_jTheta : Formalism.FourierDecayAlt.JF.JTheta := Formalism.FourierDecayAlt.P.invariant_operator_under_jacquet
theorem radialComponentIntertwines_true : Formalism.FourierDecayAlt.JF.RadialPartIntertwines := Formalism.FourierDecayAlt.P.jacquet_invariant_operator_ae
theorem jf_jqSmooth : Formalism.FourierDecayAlt.JF.JqSmooth := Formalism.FourierDecayAlt.P.jacquet_smooth_coordinates
theorem jf_cVUnderInt : Formalism.FourierDecayAlt.JF.CVUnderInt := Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral
theorem qx_besselCommutes : Formalism.FourierDecayAlt.Q.BesselCommutes := Formalism.FourierDecayAlt.P.casimir_commutes_bessel
theorem qx_eigenBessel : Formalism.FourierDecayAlt.Q.EigenBessel := Formalism.FourierDecayAlt.P.casimir_eigenvalue_bessel
theorem qx_rTTUpper : Formalism.FourierDecayAlt.Q.RTTUpper := Formalism.FourierDecayAlt.P.right_transfer_upper_levels
theorem qx_rTTLevel : Formalism.FourierDecayAlt.Q.RTTLevel := Formalism.FourierDecayAlt.P.right_transfer_all_levels
theorem qx_detLevel : Formalism.FourierDecayAlt.Q.DetLevel := Formalism.FourierDecayAlt.P.determinant_identity_all_levels
theorem qx_actualOpsExist : Formalism.FourierDecayAlt.Q.ActualOpsExist := Formalism.FourierDecayAlt.P.actual_operators_exist
theorem qx_actualAdjoint : Formalism.FourierDecayAlt.Q.ActualAdjoint := Formalism.FourierDecayAlt.P.actual_adjointness
theorem qx_actualStart : Formalism.FourierDecayAlt.Q.ActualStart := Formalism.FourierDecayAlt.P.actual_start
theorem fibre_unit_property : Formalism.FourierDecayAlt.C6.FibUnit := Formalism.FourierDecayAlt.P.fibre_unit_normalization
theorem fibre_cost : Formalism.FourierDecayAlt.C6.FibCost := Formalism.FourierDecayAlt.P.fibre_cost_estimate
theorem fibre_cost_of_parts : Formalism.FourierDecayAlt.C6.FibCostOfParts := Formalism.FourierDecayAlt.P.c6_fib_cost_of_pieces
theorem budget_class : Formalism.FourierDecayAlt.C6.BudgetClass := Formalism.FourierDecayAlt.P.budget_class_estimate
theorem discriminant_mean : Formalism.FourierDecayAlt.C6.DiscMean := Formalism.FourierDecayAlt.P.disc_mean_value
theorem s_flag : Formalism.FourierDecayAlt.C2.SFlag := Formalism.FourierDecayAlt.P.standard_flag_property
theorem gramBlocks_true : Formalism.FourierDecayAlt.C2.GramBlocks := Formalism.FourierDecayAlt.P.gram_block_form
theorem majorant_true : Formalism.FourierDecayAlt.C2.Majorant := Formalism.FourierDecayAlt.P.majorant_estimate
theorem norm_inverse : Formalism.FourierDecayAlt.C2.NormInv := Formalism.FourierDecayAlt.P.norm_of_inverse
theorem lower_split : Formalism.FourierDecayAlt.C2.LowSplit := Formalism.FourierDecayAlt.P.lower_triangular_splitting
theorem upperSplit_true : Formalism.FourierDecayAlt.C2.UpSplit := Formalism.FourierDecayAlt.P.upper_splitting
theorem upper_minor : Formalism.FourierDecayAlt.C2.MinorU := Formalism.FourierDecayAlt.P.upper_minor_identity
theorem lower_minor_bound : Formalism.FourierDecayAlt.C2.MinorL := Formalism.FourierDecayAlt.P.lower_minor_identity
theorem monomialFactorizationBound_true : Formalism.FourierDecayAlt.C2.MonomialFactorizationBound := Formalism.FourierDecayAlt.P.monomial_factorization_bound
theorem tau_membership : Formalism.FourierDecayAlt.C2.TauMem := Formalism.FourierDecayAlt.P.c2_tau_mem
theorem tau_section_bound : Formalism.FourierDecayAlt.C2.TauBound := Formalism.FourierDecayAlt.P.tau_norm_bound
theorem section_decomposition_of_parts : Formalism.FourierDecayAlt.C2.SectionDecompOfParts := Formalism.FourierDecayAlt.P.c2_section_decomp_of_pieces
theorem z_hat_section : Formalism.FourierDecayAlt.C2.ZhatSection := Formalism.FourierDecayAlt.P.zhat_section_exists
theorem z_hat_section_of_parts : Formalism.FourierDecayAlt.C2.ZhatSectionOfParts := Formalism.FourierDecayAlt.P.zhat_section_of_parts
theorem z_hat_bound : Formalism.FourierDecayAlt.C2.ZhatBound := Formalism.FourierDecayAlt.P.zhat_norm_bound
theorem fix_frame : Formalism.FourierDecayAlt.C2.FixFrame := Formalism.FourierDecayAlt.P.fixed_frame_property
theorem fibre_orbit_of_parts : Formalism.FourierDecayAlt.C2.FibreOrbitOfParts := Formalism.FourierDecayAlt.P.fibreOrbitOfParts_statement
theorem fibre_stabiliser : Formalism.FourierDecayAlt.C2.FibreStab := Formalism.FourierDecayAlt.P.fibre_stabilizer
theorem root_change_of_variables : Formalism.FourierDecayAlt.C2.RootCOV := Formalism.FourierDecayAlt.P.rootCOV_statement
theorem linearChangeOfVariables_true : Formalism.FourierDecayAlt.C2.LinCOV := Formalism.FourierDecayAlt.P.linear_change_of_variables_bis
theorem weight_four_density : Formalism.FourierDecayAlt.C2.SliceDensityIndependent := Formalism.FourierDecayAlt.P.slice_density_independent
theorem sliceDensity_of_changeOfVariables : Formalism.FourierDecayAlt.C2.SliceDensityOfChangeOfVariables := Formalism.FourierDecayAlt.P.fourth_weight_density_of_parts
theorem composition_of_positive_differentials : Formalism.FourierDecayAlt.C6.ComposeDDPlus := Formalism.FourierDecayAlt.P.compose_differential_operators
theorem commuting_involution_large_rank : Formalism.FourierDecayAlt.C6.JCommuteBig := Formalism.FourierDecayAlt.P.orbital_integral_commutes_large
theorem finite_order_intersection_in_smooth : Formalism.FourierDecayAlt.C2.FiniteOrderIntersectionInSmooth := Formalism.FourierDecayAlt.P.rule_A1_of_derivatives
theorem rule_a2 : Formalism.FourierDecayAlt.C2.SmoothClassInFiniteOrder := Formalism.FourierDecayAlt.P.rule_A2_derivatives
theorem rule_b : Formalism.FourierDecayAlt.C2.RuleB := Formalism.FourierDecayAlt.P.rule_B_derivatives
theorem lower_split_measure_identity : Formalism.FourierDecayAlt.C2.LowSplitMeas := Formalism.FourierDecayAlt.P.lower_splitting_measurable
theorem d_ptPermSpec : Formalism.FourierDecayAlt.D.PtPermSpec := Formalism.FourierDecayAlt.P.ptPerm_spec
theorem d_ptGSpec : Formalism.FourierDecayAlt.D.PtGSpec := Formalism.FourierDecayAlt.P.ptG_spec
theorem d_orbJOfData : Formalism.FourierDecayAlt.D.OrbJOfData := Formalism.FourierDecayAlt.P.orbital_transfer_of_data
theorem d_orbJIndep : Formalism.FourierDecayAlt.D.OrbJIndep := Formalism.FourierDecayAlt.P.orbital_integral_indep_choice
theorem d_orbDataOfParts : Formalism.FourierDecayAlt.D.OrbDataOfParts := Formalism.FourierDecayAlt.P.orbital_data_of_parts
theorem d_ptRelevant : Formalism.FourierDecayAlt.D.PtRelevant := Formalism.FourierDecayAlt.P.relevant_points_holds
theorem d_muNHaar : Formalism.FourierDecayAlt.D.MuNHaar := Formalism.FourierDecayAlt.P.nilpotent_measure_is_haar
theorem d_nhatCovol : Formalism.FourierDecayAlt.D.NhatCovol := Formalism.FourierDecayAlt.P.unipotent_dual_lattice_covolume
theorem d_towerExists : Formalism.FourierDecayAlt.D.TowerExists := Formalism.FourierDecayAlt.P.exists_level_tower
theorem d_moduleOfWdOn : Formalism.FourierDecayAlt.D.ModuleOfWdOn := Formalism.FourierDecayAlt.P.module_of_words
theorem d_goodOfAdm : Formalism.FourierDecayAlt.D.GoodOfAdm := Formalism.FourierDecayAlt.P.good_of_admissible
theorem d_lemmaEOfRR0 : Formalism.FourierDecayAlt.D.LemmaEOfRR0 := Formalism.FourierDecayAlt.P.lemma_E_of_residue
theorem d_thmPPosOfForms : Formalism.FourierDecayAlt.D.ThmPPosOfForms := Formalism.FourierDecayAlt.P.positivity_of_forms
theorem d_thmPPosOfModule : Formalism.FourierDecayAlt.D.ThmPPosOfModule := Formalism.FourierDecayAlt.P.positivity_of_module
theorem ma_hahnLaws : Formalism.FourierDecayAlt.MA.HahnLaws := Formalism.FourierDecayAlt.P.hahn_laws_hold
theorem ma_hahnJoint : Formalism.FourierDecayAlt.MA.HahnJoint := Formalism.FourierDecayAlt.P.hahn_joint
theorem ma_levelExistsD : Formalism.FourierDecayAlt.MA.LevelExistsD := Formalism.FourierDecayAlt.P.level_exists_alt
theorem ma_levelStarD : Formalism.FourierDecayAlt.MA.LevelStarD := Formalism.FourierDecayAlt.P.level_star_holds
theorem ma_startOKD : Formalism.FourierDecayAlt.MA.StartOKD := Formalism.FourierDecayAlt.P.start_admissible
theorem ma_sitesOKD : Formalism.FourierDecayAlt.MA.SitesOKD := Formalism.FourierDecayAlt.P.sites_admissible
theorem admissible_joint : Formalism.FourierDecayAlt.MA.AdmJoint := Formalism.FourierDecayAlt.P.admissible_joint_alt
theorem ma_modelFrameDOfParts : Formalism.FourierDecayAlt.MA.ModelFrameDOfParts := Formalism.FourierDecayAlt.P.model_frame_of_parts
theorem ma_anLeibniz : Formalism.FourierDecayAlt.MA.AnLeibniz := Formalism.FourierDecayAlt.P.analytic_leibniz
theorem ma_anCoord : Formalism.FourierDecayAlt.MA.AnCoord := Formalism.FourierDecayAlt.P.analytic_coordinates
theorem ma_anComm : Formalism.FourierDecayAlt.MA.AnComm := Formalism.FourierDecayAlt.P.analytic_commutation
theorem ma_anUnits : Formalism.FourierDecayAlt.MA.AnUnits := Formalism.FourierDecayAlt.P.analytic_units_hold
theorem ma_anNontrivial : Formalism.FourierDecayAlt.MA.AnNontrivial := Formalism.FourierDecayAlt.P.analytic_nontrivial
theorem ma_anLawsOfParts : Formalism.FourierDecayAlt.MA.AnLawsOfParts := Formalism.FourierDecayAlt.P.analytic_laws_of_parts
theorem ma_anLaws : Formalism.FourierDecayAlt.MA.AnLaws := Formalism.FourierDecayAlt.P.analytic_laws
theorem ma_modelFrameAnOfParts : Formalism.FourierDecayAlt.MA.ModelFrameAnOfParts := Formalism.FourierDecayAlt.P.model_frame_analytic_of_parts
theorem ma_modelFrameD : Formalism.FourierDecayAlt.MA.ModelFrameD := Formalism.FourierDecayAlt.P.model_frame_algebra
theorem ma_modelFrameAn : Formalism.FourierDecayAlt.MA.ModelFrameAn := Formalism.FourierDecayAlt.P.model_frame_analytic
theorem d_levelZero : Formalism.FourierDecayAlt.D.LevelZero := Formalism.FourierDecayAlt.P.level_zero_holds
theorem rule_c : Formalism.FourierDecayAlt.C2.RuleC := Formalism.FourierDecayAlt.P.rule_C_derivatives
theorem nf_tCoordComm : Formalism.FourierDecayAlt.NF.TCoordComm := Formalism.FourierDecayAlt.P.level_coordinates_commute
theorem nf_actualPreLevel : Formalism.FourierDecayAlt.NF.ActualPreLevel := Formalism.FourierDecayAlt.P.actual_pre_level
theorem nf_relIsCoreNorm : Formalism.FourierDecayAlt.NF.RelIsCoreNorm := Formalism.FourierDecayAlt.P.relations_core_and_norms
theorem twoSided_true : Formalism.FourierDecayAlt.C2.TwoSided := Formalism.FourierDecayAlt.P.two_sided_derivative_rule
theorem gram_independent_signature : Formalism.FourierDecayAlt.C2.GramIndependentSignature := Formalism.FourierDecayAlt.P.gram_independent_signature'
theorem polynomial_proper : Formalism.FourierDecayAlt.C2.PolyProper := Formalism.FourierDecayAlt.P.polynomial_map_proper
theorem jc_lemmaEOfModel : Formalism.FourierDecayAlt.JC.LemmaEOfModel := Formalism.FourierDecayAlt.P.lemma_E_of_model
theorem jc_cutFSmooth : Formalism.FourierDecayAlt.JC.CutFSmooth := Formalism.FourierDecayAlt.P.cutoff_smooth
theorem theorem_p1_of_places : Formalism.FourierDecayAlt.JC.PlaneExponentialBoundOfPlaces := Formalism.FourierDecayAlt.P.plane_exponential_bound_of_places
theorem offDiagonalLiftBound_of_places : Formalism.FourierDecayAlt.JC.OffDiagonalLiftBoundOfPlaces := Formalism.FourierDecayAlt.P.off_diagonal_lift_bound_of_places
theorem jc_corollaryTOfSumForm : Formalism.FourierDecayAlt.JC.CorollaryTOfSumForm := Formalism.FourierDecayAlt.P.corollary_T_of_sum_form
theorem theta_existence : Formalism.FourierDecayAlt.JC.ThetaExistence₂ := Formalism.FourierDecayAlt.P.jc_theta_exists_variant
theorem jc_thmPIntOfPlaces : Formalism.FourierDecayAlt.JC.ThmPIntOfPlaces := Formalism.FourierDecayAlt.P.theorem_P_integral_of_places
theorem jc_propGramOfPlaces : Formalism.FourierDecayAlt.JC.PropGramOfPlaces := Formalism.FourierDecayAlt.P.gram_proposition_of_places
theorem jc_gramPlaceBuilt : Formalism.FourierDecayAlt.JC.GramPlaceBuilt := Formalism.FourierDecayAlt.P.gram_at_built_place
theorem jc_orbJCutScalar : Formalism.FourierDecayAlt.JC.OrbJCutScalar := Formalism.FourierDecayAlt.P.orbital_integral_cutoff_scalar
theorem jc_mkDataInst : Formalism.FourierDecayAlt.JC.MkDataInst := Formalism.FourierDecayAlt.P.concrete_data_instance
theorem jc_sizesConcreteOfParts : Formalism.FourierDecayAlt.JC.SizesConcreteOfParts := Formalism.FourierDecayAlt.P.concrete_sizes_of_parts
theorem jc_axiomsConcrete : Formalism.FourierDecayAlt.JC.AxiomsConcrete := Formalism.FourierDecayAlt.P.concrete_axioms
theorem condition_c1_ii : Formalism.FourierDecayAlt.C2.C1ii := Formalism.FourierDecayAlt.P.stabilizer_split
theorem condition_c1_iii : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree := Formalism.FourierDecayAlt.P.stabilizer_pairs
theorem section_decomposition : Formalism.FourierDecayAlt.C2.SectionDecomp := Formalism.FourierDecayAlt.P.c2_section_decomp
theorem mirror_decomposition : Formalism.FourierDecayAlt.C2.MirrorDecomp := Formalism.FourierDecayAlt.P.mirrorDecomp_statement
theorem nf_sBlock : Formalism.FourierDecayAlt.NF.SBlock := Formalism.FourierDecayAlt.P.shift_block
theorem nf_sConn : Formalism.FourierDecayAlt.NF.SConn := Formalism.FourierDecayAlt.P.shift_connection
theorem nf_sNorm : Formalism.FourierDecayAlt.NF.SNorm := Formalism.FourierDecayAlt.P.shift_norm
theorem nf_thmSOfSteps : Formalism.FourierDecayAlt.NF.ThmSOfSteps := Formalism.FourierDecayAlt.P.theorem_S_of_steps
theorem nf_thmSRing : Formalism.FourierDecayAlt.NF.ThmSRing := Formalism.FourierDecayAlt.P.theorem_S_ring
theorem b_xiExists : Formalism.FourierDecayAlt.B.XiExists := Formalism.FourierDecayAlt.P.exists_auxiliary_xi
theorem fibre_orbit : Formalism.FourierDecayAlt.C2.FibreOrbit := Formalism.FourierDecayAlt.P.fibre_orbit_description
theorem ma_adjGens : Formalism.FourierDecayAlt.MA.AdjGens := Formalism.FourierDecayAlt.P.adjoint_generators
theorem ma_adjClosed : Formalism.FourierDecayAlt.MA.AdjClosed := Formalism.FourierDecayAlt.P.adjoint_closed
theorem ma_adjAlg : Formalism.FourierDecayAlt.MA.AdjAlg := Formalism.FourierDecayAlt.P.adjoint_algebra
theorem ma_adjAlgOfParts : Formalism.FourierDecayAlt.MA.AdjAlgOfParts := Formalism.FourierDecayAlt.P.adjoint_algebra_of_parts
theorem ma_adjMatrix : Formalism.FourierDecayAlt.MA.AdjMatrix := Formalism.FourierDecayAlt.P.adjoint_matrix
theorem ma_measureJoint : Formalism.FourierDecayAlt.MA.MeasureJoint := Formalism.FourierDecayAlt.P.measure_joint
theorem ma_jnNorm : Formalism.FourierDecayAlt.MA.JnNorm := Formalism.FourierDecayAlt.P.jacobi_norm
theorem ma_jAdjZero : Formalism.FourierDecayAlt.MA.JAdjZero := Formalism.FourierDecayAlt.P.adjoint_at_zero
theorem ma_hypsNonvacuous : Formalism.FourierDecayAlt.MA.HypsNonvacuous := Formalism.FourierDecayAlt.P.hypotheses_nonvacuous
theorem ma_modelWordsD : Formalism.FourierDecayAlt.MA.ModelWordsD := Formalism.FourierDecayAlt.P.model_words
theorem ma_factorChosen : Formalism.FourierDecayAlt.MA.FactorChosen := Formalism.FourierDecayAlt.P.factor_chosen
theorem ma_famRestQ : Formalism.FourierDecayAlt.MA.FamRestQ := Formalism.FourierDecayAlt.P.family_restriction
theorem ma_famImportsQOfParts : Formalism.FourierDecayAlt.MA.FamImportsQOfParts := Formalism.FourierDecayAlt.P.family_imports_of_parts
theorem ma_thmPQOfParts : Formalism.FourierDecayAlt.MA.ThmPQOfParts := Formalism.FourierDecayAlt.P.theorem_P_of_parts
theorem ma_lemmaEModelOfParts : Formalism.FourierDecayAlt.MA.LemmaEModelOfParts := Formalism.FourierDecayAlt.P.lemma_model_of_parts
theorem ma_rootsOutQOfParts : Formalism.FourierDecayAlt.MA.RootsOutQOfParts := Formalism.FourierDecayAlt.P.roots_outside_of_parts_alt
theorem ma_stepImportsQOfParts : Formalism.FourierDecayAlt.MA.StepImportsQOfParts := Formalism.FourierDecayAlt.P.induction_imports_of_parts
theorem ma_i3QOfParts : Formalism.FourierDecayAlt.MA.EnergyAbsoluteIdentityFromComponents := Formalism.FourierDecayAlt.P.third_identity_of_parts
theorem degree_count_second : Formalism.FourierDecayAlt.C7.DegreeCount2 := Formalism.FourierDecayAlt.P.hermitian_curvature_degree_count
theorem lemma_b3_count_second : Formalism.FourierDecayAlt.C7.LetterProductDoubleDegreeCount := Formalism.FourierDecayAlt.P.third_count_lemma_variant
theorem dualityPositiveSubspace_true : Formalism.FourierDecayAlt.FormPairingAction.DualityPositiveSubspace := Formalism.FourierDecayAlt.P.duality_positive_subspace
theorem dualKernelSubmodule_true : Formalism.FourierDecayAlt.FormPairingAction.LemmaDKSub := Formalism.FourierDecayAlt.P.dual_kernel_lemma_restricted
theorem nf_modelSHyp : Formalism.FourierDecayAlt.NF.ModelSHyp := Formalism.FourierDecayAlt.P.model_hypotheses
theorem nf_normalFormOfS : Formalism.FourierDecayAlt.NF.NormalFormOfS := Formalism.FourierDecayAlt.P.normal_form_of_S
theorem nf_normalFormFromModuleOfParts : Formalism.FourierDecayAlt.NF.NormalFormFromModuleOfParts := Formalism.FourierDecayAlt.P.normal_form_from_module
theorem nf_actualSHypOfParts : Formalism.FourierDecayAlt.NF.ActualSHypOfParts := Formalism.FourierDecayAlt.P.actual_hypotheses_of_parts
theorem nf_actualSHyp : Formalism.FourierDecayAlt.NF.ActualSHyp := Formalism.FourierDecayAlt.P.actual_spectral_hypotheses
theorem qx_normalFormFromModule : Formalism.FourierDecayAlt.Q.NormalFormFromModule := Formalism.FourierDecayAlt.P.normalFormFromModule_statement
theorem qx_normalFormActual : Formalism.FourierDecayAlt.Q.NormalFormActual := Formalism.FourierDecayAlt.P.normal_form_actual
theorem qx_levelStartActual : Formalism.FourierDecayAlt.Q.LevelStartActual := Formalism.FourierDecayAlt.P.level_start_actual
theorem d_muRHaar : Formalism.FourierDecayAlt.D.MuRHaar := Formalism.FourierDecayAlt.P.radial_measure_is_haar
theorem d_dFrameExists : Formalism.FourierDecayAlt.D.DFrameExists := Formalism.FourierDecayAlt.P.exists_isotropic_frame
theorem d_sliceOm : Formalism.FourierDecayAlt.D.SliceOm := Formalism.FourierDecayAlt.P.slice_measure_identity
theorem d_muNSplit : Formalism.FourierDecayAlt.D.MuNSplit := Formalism.FourierDecayAlt.P.unipotent_measure_splitting
theorem nf_mulZExists : Formalism.FourierDecayAlt.NF.MulZExists := Formalism.FourierDecayAlt.P.multiplication_zeta_exists
theorem nf_actualZetaSmooth : Formalism.FourierDecayAlt.NF.ActualZetaSmooth := Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt
theorem nf_nFOrder0 : Formalism.FourierDecayAlt.NF.NFOrder0 := Formalism.FourierDecayAlt.P.normal_form_order_zero
theorem nf_nFOrder0OfParts : Formalism.FourierDecayAlt.NF.NFOrder0OfParts := Formalism.FourierDecayAlt.P.normal_form_order_zero_of_parts
theorem nf_sExtra : Formalism.FourierDecayAlt.NF.SExtra := Formalism.FourierDecayAlt.P.shift_extra
theorem d_vecVIndep : Formalism.FourierDecayAlt.D.VecVIndep := Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep
theorem jct_realInputsBuilt : Formalism.FourierDecayAlt.JCT.RealInputsBuilt := Formalism.FourierDecayAlt.P.real_inputs_built
theorem jct_theoremABuilt : Formalism.FourierDecayAlt.JCT.TheoremABuilt := Formalism.FourierDecayAlt.P.theorem_A_built
theorem jct_realInputsBuiltClosed : Formalism.FourierDecayAlt.JCT.RealInputsBuiltClosed := Formalism.FourierDecayAlt.P.real_inputs_built_closed_form
theorem jct_energyOfLemmaE : Formalism.FourierDecayAlt.JCT.EnergyOfLemmaE := Formalism.FourierDecayAlt.P.energy_of_built_setting
theorem d_orbJConv : Formalism.FourierDecayAlt.D.OrbJConv := Formalism.FourierDecayAlt.P.orbital_integral_converges
theorem jct_levelsActualBuilt : Formalism.FourierDecayAlt.JCT.LevelsActualBuilt := Formalism.FourierDecayAlt.P.levels_of_built_setting
theorem top_vecVTypes : Formalism.FourierDecayAlt.Top.VecVTypes := Formalism.FourierDecayAlt.P.vector_valued_types
theorem top_typeProjExists : Formalism.FourierDecayAlt.Top.TypeProjExists := Formalism.FourierDecayAlt.P.type_projectors_exist
theorem top_topOfEmpty : Formalism.FourierDecayAlt.Top.TopOfEmpty := Formalism.FourierDecayAlt.P.top_of_empty
theorem top_topOfRadial : Formalism.FourierDecayAlt.Top.TopOfRadial := Formalism.FourierDecayAlt.P.top_of_radial
theorem top_inputsTOfInputs : Formalism.FourierDecayAlt.Top.InputsTOfInputs := Formalism.FourierDecayAlt.P.typed_inputs_of_inputs
theorem top_realInputsBuiltClosedT : Formalism.FourierDecayAlt.Top.RealInputsBuiltClosedT := Formalism.FourierDecayAlt.P.real_inputs_closed_typed
theorem nf_radRedMem : Formalism.FourierDecayAlt.NF.RadRedMem := Formalism.FourierDecayAlt.P.radical_reduction_mem
theorem nf_radRedInj : Formalism.FourierDecayAlt.NF.RadRedInj := Formalism.FourierDecayAlt.P.radical_reduction_injective
theorem nf_radOrder0 : Formalism.FourierDecayAlt.NF.RadOrder0 := Formalism.FourierDecayAlt.P.radical_order_zero
theorem nf_radRedSurj : Formalism.FourierDecayAlt.NF.RadRedSurj := Formalism.FourierDecayAlt.P.radical_reduction_surjective
theorem PBA.pb_blockOfCS : Formalism.FourierDecayAlt.KB.BlockOfCS := Formalism.FourierDecayAlt.P.PBA.block_of_cauchy_schwarz
theorem PBA.pb_blockSchur : Formalism.FourierDecayAlt.KB.BlockSchur := Formalism.FourierDecayAlt.P.PBA.blockSchur_true
theorem PBA.pb_liftOfLoc : Formalism.FourierDecayAlt.KB.LiftOfLoc := Formalism.FourierDecayAlt.P.PBA.liftOfLoc_statement
theorem PBA.pb_topOfLoc : Formalism.FourierDecayAlt.KB.TopOfLoc := Formalism.FourierDecayAlt.P.PBA.top_of_local
theorem PBA.pb_limitClosed : Formalism.FourierDecayAlt.KB.LimitClosed := Formalism.FourierDecayAlt.P.PBA.limit_closed
theorem pb_thetaCpt : Formalism.FourierDecayAlt.KB.ThetaCpt := Formalism.FourierDecayAlt.P.theta_compact_support
theorem ma_factorExistsQ : Formalism.FourierDecayAlt.MA.FactorExistsQ := Formalism.FourierDecayAlt.P.factor_exists
theorem ma_measQ : Formalism.FourierDecayAlt.MA.MeasQ := Formalism.FourierDecayAlt.P.measure_regular
theorem ma_wPosQ : Formalism.FourierDecayAlt.MA.WPosQ := Formalism.FourierDecayAlt.P.weight_positive
theorem ma_pRegQ : Formalism.FourierDecayAlt.MA.PRegQ := Formalism.FourierDecayAlt.P.polynomial_regular
theorem ma_pRatioQ : Formalism.FourierDecayAlt.MA.PRatioQ := Formalism.FourierDecayAlt.P.probability_ratio
theorem ma_i3Signed : Formalism.FourierDecayAlt.MA.SignedEnergyIdentity := Formalism.FourierDecayAlt.P.third_identity_signed
theorem ma_i3Q : Formalism.FourierDecayAlt.MA.EnergyAbsoluteIdentity := Formalism.FourierDecayAlt.P.third_identity
theorem ma_adjBQ : Formalism.FourierDecayAlt.MA.AdjBQ := Formalism.FourierDecayAlt.P.adjoint_bounded
theorem ma_jetQ : Formalism.FourierDecayAlt.MA.JetQ := Formalism.FourierDecayAlt.P.jet_module_closed
theorem ma_i4Q : Formalism.FourierDecayAlt.MA.EnergyPolynomialInParameter := Formalism.FourierDecayAlt.P.fourth_identity
theorem ma_i4'Q : Formalism.FourierDecayAlt.MA.I4'Q := Formalism.FourierDecayAlt.P.fourth_identity_dual
theorem ma_i5aQ : Formalism.FourierDecayAlt.MA.EnergyShiftDifference := Formalism.FourierDecayAlt.P.fifth_identity_first
theorem ma_residuesQ : Formalism.FourierDecayAlt.MA.ResiduesQ := Formalism.FourierDecayAlt.P.residuesAlt
theorem ma_weightRatioQ : Formalism.FourierDecayAlt.MA.WeightRatioQ := Formalism.FourierDecayAlt.P.weight_ratio
theorem ma_stepImportsQ : Formalism.FourierDecayAlt.MA.StepImportsQ := Formalism.FourierDecayAlt.P.induction_imports
theorem ma_famImportsQ : Formalism.FourierDecayAlt.MA.FamImportsQ := Formalism.FourierDecayAlt.P.family_imports
theorem ma_rootsOutQ : Formalism.FourierDecayAlt.MA.RootsOutQ := Formalism.FourierDecayAlt.P.roots_outside
theorem ma_i1Q : Formalism.FourierDecayAlt.MA.EnergyPolynomialInPoints := Formalism.FourierDecayAlt.P.first_identity
theorem sourceSquareIntegrable_true : Formalism.FourierDecayAlt.MA.SourceSquareIntegrable := Formalism.FourierDecayAlt.P.jacobi_square_integrable
theorem empty_word_energy_density : Formalism.FourierDecayAlt.MA.EmptyWordEnergyDensity := Formalism.FourierDecayAlt.P.jacobi_base
theorem ma_thmPForm : Formalism.FourierDecayAlt.MA.ThmPForm := Formalism.FourierDecayAlt.P.theorem_P_form
theorem ma_thmPAdj : Formalism.FourierDecayAlt.MA.ThmPAdj := Formalism.FourierDecayAlt.P.theorem_P_adjoint
theorem ma_thmPGw : Formalism.FourierDecayAlt.MA.ThmPGw := Formalism.FourierDecayAlt.P.theorem_P_weight
theorem ma_thmPQ : Formalism.FourierDecayAlt.MA.ThmPQ := Formalism.FourierDecayAlt.P.theorem_P
theorem ma_lemmaEModel : Formalism.FourierDecayAlt.MA.LemmaEModel := Formalism.FourierDecayAlt.P.lemma_model
theorem tbb_stepOne : Formalism.FourierDecayAlt.TBB.StepOne := Formalism.FourierDecayAlt.P.lemma_s_induction_base
theorem tbb_stepUp : Formalism.FourierDecayAlt.TBB.StepUp := Formalism.FourierDecayAlt.P.lemma_s_induction_up
theorem tbb_lemmaSOfSteps : Formalism.FourierDecayAlt.TBB.LemmaSOfSteps := Formalism.FourierDecayAlt.P.lemma_s_of_parts
theorem tbb_corSOfLemmaS : Formalism.FourierDecayAlt.TBB.CorSOfLemmaS := Formalism.FourierDecayAlt.P.corSOfLemmaS_statement
theorem pb_waveOfLoc : Formalism.FourierDecayAlt.KB.WaveOfLoc := Formalism.FourierDecayAlt.P.plane_wave_bound_of_local_bounds
theorem pb_limitInt : Formalism.FourierDecayAlt.KB.LimitInt := Formalism.FourierDecayAlt.P.integral_formula_passes_to_limits
theorem pb_headAlg : Formalism.FourierDecayAlt.KB.HeadAlg := Formalism.FourierDecayAlt.P.head_algebra_relations
theorem pb_kloostDens : Formalism.FourierDecayAlt.KB.KloostDens := Formalism.FourierDecayAlt.P.kloosterman_density
theorem top_topPSDT : Formalism.FourierDecayAlt.Top.TopPSDT := Formalism.FourierDecayAlt.P.top_positive_semidefinite
theorem real_inputs_closed_leading_form : Formalism.FourierDecayAlt.KB.RealInputsClosedLeadingForm := Formalism.FourierDecayAlt.P.real_inputs_closed_model_place
theorem real_inputs_closed_admissible_settings : Formalism.FourierDecayAlt.KB.RealInputsClosedAdmissibleSettings := Formalism.FourierDecayAlt.P.real_inputs_closed_model_place_two
theorem tbb_ptBoundOfCorS : Formalism.FourierDecayAlt.TBB.PtBoundOfCorS := Formalism.FourierDecayAlt.P.point_bound_of_corollary_s
theorem tbb_vecCutAll : Formalism.FourierDecayAlt.TBB.VecCutAll := Formalism.FourierDecayAlt.P.vector_truncation_all_places
theorem tbb_thmBpOfParts : Formalism.FourierDecayAlt.TBB.ThmBpOfParts := Formalism.FourierDecayAlt.P.theorem_b_of_parts
theorem tbb_triAt : Formalism.FourierDecayAlt.TBB.TriAt := Formalism.FourierDecayAlt.P.triangle_inequality_at_place
theorem pb_phiZero : Formalism.FourierDecayAlt.KB.PhiZero := Formalism.FourierDecayAlt.P.phi_zero_hermitian_curvature
theorem pb_densC : Formalism.FourierDecayAlt.KB.DensC := Formalism.FourierDecayAlt.P.density_constant
theorem pb_sumFormOfLoc : Formalism.FourierDecayAlt.KB.SumFormOfLoc := Formalism.FourierDecayAlt.P.sum_form_of_local_statements

end Formalism.FourierDecayAlt.Final
