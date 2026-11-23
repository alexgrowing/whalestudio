import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyPuncturedAffineLine
import Development.AutomorphicArithmetic.CommutativeAlgebra.DescentOfIntegralDescentTruncation
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleFinitePresentationModelExists
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CofilteredSchemeLimitExistsLocally
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteOverHenselianFibreIdempotentsLift
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleMayerVietorisLongExact
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleMayerVietorisShortExact
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AugmentationMapBijective
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveLineChartsOfHenselianFinite
import Development.EtaleCohomology.EtaleSheaves.AICAcycPf
import Development.EtaleCohomology.EtaleSheaves.AICOpenPf
import Development.EtaleCohomology.EtaleSheaves.NonunitCase
import Development.EtaleCohomology.EtaleSheaves.AugBijPf
import Development.EtaleCohomology.EtaleSheaves.AlgebraicIntegralClosure
import Development.EtaleCohomology.EtaleSheaves.BaseIntPf
import Development.EtaleCohomology.EtaleSheaves.BaseLocLocPf
import Development.EtaleCohomology.EtaleSheaves.BinPfChains
import Development.EtaleCohomology.EtaleSheaves.BuildCut
import Development.EtaleCohomology.EtaleSheaves.ChartAcycPf
import Development.EtaleCohomology.EtaleSheaves.ChartBCNnmPf
import Development.EtaleCohomology.EtaleSheaves.ChartsGeomVpaPf
import Development.EtaleCohomology.EtaleSheaves.ChaseBPf
import Development.EtaleCohomology.EtaleSheaves.ChasePf
import Development.EtaleCohomology.EtaleSheaves.ChowCut
import Development.EtaleCohomology.EtaleSheaves.ChowGraphCut
import Development.EtaleCohomology.EtaleSheaves.ChowLCut
import Development.EtaleCohomology.EtaleSheaves.ColimHensPf
import Development.EtaleCohomology.EtaleSheaves.CompCut
import Development.EtaleCohomology.EtaleSheaves.ContAffPf
import Development.EtaleCohomology.EtaleSheaves.ContIndPf
import Development.EtaleCohomology.EtaleSheaves.ContPf
import Development.EtaleCohomology.EtaleSheaves.ContStepPf
import Development.EtaleCohomology.EtaleSheaves.AicschOfImm
import Development.EtaleCohomology.EtaleSheaves.CoverCut
import Development.EtaleCohomology.EtaleSheaves.CoverExistence
import Development.EtaleCohomology.EtaleSheaves.DescEqvPf
import Development.EtaleCohomology.EtaleSheaves.DiagCompPf
import Development.EtaleCohomology.EtaleSheaves.DiagIdPf
import Development.EtaleCohomology.EtaleSheaves.DiagNatPf
import Development.EtaleCohomology.EtaleSheaves.EmbedNonDegOf
import Development.EtaleCohomology.EtaleSheaves.EtaleEmbedding
import Development.EtaleCohomology.EtaleSheaves.EtaleEmbedding.EmbedOfLines
import Development.EtaleCohomology.EtaleSheaves.EmptyH2
import Development.EtaleCohomology.EtaleSheaves.FMrangePfQc
import Development.EtaleCohomology.EtaleSheaves.FibClosedPf
import Development.EtaleCohomology.EtaleSheaves.FibCovPf
import Development.EtaleCohomology.EtaleSheaves.FibMapRange
import Development.EtaleCohomology.EtaleSheaves.FibClosed
import Development.EtaleCohomology.EtaleSheaves.FibStalkPf
import Development.EtaleCohomology.EtaleSheaves.FibreEqvPf
import Development.EtaleCohomology.EtaleSheaves.FiltPf
import Development.EtaleCohomology.EtaleSheaves.FlatMonoLimPf
import Development.EtaleCohomology.EtaleSheaves.ResSmulGen
import Development.EtaleCohomology.EtaleSheaves.EmbedNonDeg
import Development.EtaleCohomology.EtaleSheaves.GeometricDataOfLines
import Development.EtaleCohomology.EtaleSheaves.GluePf
import Development.EtaleCohomology.EtaleSheaves.HZeroPf
import Development.EtaleCohomology.EtaleSheaves.HasLimPf
import Development.EtaleCohomology.EtaleSheaves.HensCut
import Development.EtaleCohomology.EtaleSheaves.IdemLiftOf
import Development.EtaleCohomology.EtaleSheaves.LZIdemSumApprox
import Development.EtaleCohomology.EtaleSheaves.IdemPartPf
import Development.EtaleCohomology.EtaleSheaves.IdemSecPf
import Development.EtaleCohomology.EtaleSheaves.ImageInPf
import Development.EtaleCohomology.EtaleSheaves.ImgOf
import Development.EtaleCohomology.EtaleSheaves.InjStepPf
import Development.EtaleCohomology.EtaleSheaves.IntFibPf
import Development.EtaleCohomology.EtaleSheaves.IntHensPf
import Development.EtaleCohomology.EtaleSheaves.IntPBPf
import Development.EtaleCohomology.EtaleSheaves.IterBCPf
import Development.EtaleCohomology.EtaleSheaves.IterCompPf
import Development.EtaleCohomology.EtaleSheaves.LCIsoPf
import Development.EtaleCohomology.EtaleSheaves.LZARStepOf
import Development.EtaleCohomology.EtaleSheaves.H1FiniteCoefficients
import Development.EtaleCohomology.EtaleSheaves.LZHensFinitePf
import Development.EtaleCohomology.EtaleSheaves.MulRightMem
import Development.EtaleCohomology.EtaleSheaves.LZIdemSumApproxYDDUPf
import Development.EtaleCohomology.EtaleSheaves.NoetherianLocalChartOverlapFiniteComplement
import Development.EtaleCohomology.EtaleSheaves.LiftPf
import Development.EtaleCohomology.EtaleSheaves.LimIntPf
import Development.EtaleCohomology.EtaleSheaves.LineChartPf
import Development.EtaleCohomology.EtaleSheaves.LineExPf
import Development.EtaleCohomology.EtaleSheaves.LineHighPf
import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
import Development.EtaleCohomology.EtaleSheaves.ProjectiveLineTwoAffineChartsPolynomialGenerated
import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineZero
import Development.EtaleCohomology.EtaleSheaves.LocACPf
import Development.EtaleCohomology.EtaleSheaves.LocalIntegralClosureRoots
import Development.EtaleCohomology.EtaleSheaves.LocalizationIntegralClosure
import Development.EtaleCohomology.EtaleSheaves.AicOfIsLocalization
import Development.EtaleCohomology.EtaleSheaves.LocPowPf
import Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence
import Development.EtaleCohomology.EtaleSheaves.MonicSplitsPf
import Development.EtaleCohomology.EtaleSheaves.UliftSmulEq
import Development.EtaleCohomology.EtaleSheaves.NbIsoPf
import Development.EtaleCohomology.EtaleSheaves.NormACPf
import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.NormAICOf
import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.AicSubsingleton
import Development.EtaleCohomology.EtaleSheaves.OpenCovPtaPf
import Development.EtaleCohomology.EtaleSheaves.OverMVPf
import Development.EtaleCohomology.EtaleSheaves.ChartMapBase
import Development.EtaleCohomology.EtaleSheaves.PartAPf
import Development.EtaleCohomology.EtaleSheaves.PartBPf
import Development.EtaleCohomology.EtaleSheaves.PartCPfSplit
import Development.EtaleCohomology.EtaleSheaves.PartDiagCut
import Development.EtaleCohomology.EtaleSheaves.PartDirectedPf
import Development.EtaleCohomology.EtaleSheaves.SimplicialPieceDiscrete
import Development.EtaleCohomology.EtaleSheaves.ProEqvPfA
import Development.EtaleCohomology.EtaleSheaves.ProdAcycPf
import Development.EtaleCohomology.EtaleSheaves.ProdPf
import Development.EtaleCohomology.EtaleSheaves.ProdACFField
import Development.EtaleCohomology.EtaleSheaves.QuotAcycCut
import Development.EtaleCohomology.EtaleSheaves.RelNormPf
import Development.EtaleCohomology.EtaleSheaves.ResBijPf
import Development.EtaleCohomology.EtaleSheaves.RestrPf
import Development.EtaleCohomology.EtaleSheaves.RootAICPf
import Development.EtaleCohomology.EtaleSheaves.RootPf
import Development.EtaleCohomology.EtaleSheaves.RootPowPf
import Development.EtaleCohomology.EtaleSheaves.SpecAICPf
import Development.EtaleCohomology.EtaleSheaves.StageBPf
import Development.EtaleCohomology.EtaleSheaves.StageProdPf
import Development.EtaleCohomology.EtaleSheaves.StalkAICRingPf
import Development.EtaleCohomology.EtaleSheaves.StalkContPf
import Development.EtaleCohomology.EtaleSheaves.StalkGermPf
import Development.EtaleCohomology.EtaleSheaves.StalkSHSPf
import Development.EtaleCohomology.EtaleSheaves.StdChartsOf
import Development.EtaleCohomology.EtaleSheaves.FibreIdem
import Development.EtaleCohomology.EtaleSheaves.SteinPf
import Development.EtaleCohomology.EtaleSheaves.KummerInduction.StepKOf
import Development.EtaleCohomology.EtaleSheaves.StepPf
import Development.EtaleCohomology.EtaleSheaves.DiagramChase.StepSOfChase
import Development.EtaleCohomology.EtaleSheaves.SurjStepPf
import Development.EtaleCohomology.EtaleSheaves.SysFMPfSys
import Development.EtaleCohomology.EtaleSheaves.SysOf
import Development.EtaleCohomology.EtaleSheaves.TowerFinPf
import Development.EtaleCohomology.EtaleSheaves.TruncationPieces
import Development.EtaleCohomology.EtaleSheaves.TruncBijPf
import Development.EtaleCohomology.EtaleSheaves.Truncation
import Development.EtaleCohomology.EtaleSheaves.AugHolds
import Development.EtaleCohomology.EtaleSheaves.TwTrivPf
import Development.EtaleCohomology.EtaleSheaves.ZCovPf
import Development.EtaleCohomology.EtaleSheaves.StalkGerm
import Development.EtaleCohomology.EtaleSheaves.ZarIndPf
import Development.EtaleCohomology.EtaleSheaves.LineHigh

namespace UpperTheory.Et.E2

theorem n3 : LateralTheory.E.TruncationPieces.Piece := @LateralTheory.E.SimplicialPieceDiscrete.Piece_of

theorem n6 : LateralTheory.E.FiltPf.TowerFin := @LateralTheory.E.FiltPf.TowerFin_of

theorem n8 : LateralTheory.E.TruncPf.TruncBij := @LateralTheory.E.TruncPf.TruncBij_of

theorem n7 : LateralTheory.E.FiltPf.Trunc := @LateralTheory.E.TruncationInclusionIso.Trunc_of @n8

theorem n5 : LateralTheory.E.FiltPf.Tower := @LateralTheory.E.FiltPf.tower_of @n6 @n7

theorem n4 : LateralTheory.E.TruncationPieces.Filt := @LateralTheory.E.TruncationPieces.Filt_of_tower @n5

theorem n2 : LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels := @LateralTheory.E.TruncationPieces.etale_relK_single_degree_pieces_of_piece_and_filtration @n3 @n4

theorem n1 : LateralTheory.E.t_E2Cut.Desc := @UpperTheory.descent_of_integral_descent_truncation @n2

theorem n11 : LateralTheory.E.BuildCut.Pts := @LateralTheory.E.PtsPf.Pts_of

theorem n12 : LateralTheory.E.BuildCut.LimInt := @LateralTheory.E.LimIntPf.LimInt_of

theorem n20 : LateralTheory.E.MayerVietorisSequence.SES := @UpperTheory.Cb.etale_mayer_vietoris_short_exact

theorem n21 : LateralTheory.E.MayerVietorisSequence.LES := @UpperTheory.Cb.etale_mayer_vietoris_long_exact

theorem n19 : LateralTheory.E.MayerVietorisSequence.MVSpc := @LateralTheory.E.MayerVietorisSequence.mvSpc_of @n20 @n21

theorem n22 : LateralTheory.E.MayerVietorisSequence.OpenCov := @LateralTheory.E.OpenCov_ptaPf.openCov

theorem n23 : LateralTheory.E.MayerVietorisSequence.SchPB := @LateralTheory.E.MayerVietorisSequence.schPB

theorem n18 : LateralTheory.E.t_E2Cut.MV := LateralTheory.E.t_E2Cut.MV_of_three n19 n22 n23

theorem n24 : LateralTheory.E.ContPf.ContAff := @LateralTheory.E.ContAffPf.ContAff_of

theorem n27 : LateralTheory.E.StepSPf.DiagramChase₂ := @LateralTheory.E.ChasePf.Chase_of

theorem n26 : LateralTheory.E.ContStepPf.StepS := @LateralTheory.E.StepSPf.StepS_of_chase @n27

theorem n29 : LateralTheory.E.StepKPf.Restr := @LateralTheory.E.RestrPf.Restr_of

theorem n30 : LateralTheory.E.StepKPf.ChasePf.ChaseB := @LateralTheory.E.ChaseBPf.ChaseB_of

theorem n28 : LateralTheory.E.ContStepPf.StepK := @LateralTheory.E.StepKPf.ChasePf.StepK_of' @n29 @n30

theorem n25 : LateralTheory.E.ContPf.ContStep := @LateralTheory.E.ContStepPf.ContStep_of @n26 @n28

theorem n31 : LateralTheory.E.ContPf.ContInd := @LateralTheory.E.ContIndPf.ContInd_of

theorem n17 : LateralTheory.E.t_E2Cut.Cont := @LateralTheory.E.ContPf.Cont_of @n18 @n24 @n25 @n31

theorem n16 : LateralTheory.E.HasLimPf.Loc := UpperTheory.Cb.cofiltered_scheme_limit_exists_locally n12 n17 n18

theorem n15 : LateralTheory.E.SysPf.HasLim := LateralTheory.E.HasLimPf.HasLim_of n16

theorem n34 : LateralTheory.E.SysFMPfSys.IdemSec := @LateralTheory.E.IdemSecPf.IdemSec_of

theorem n35 : LateralTheory.E.SysFMPf.FMex := UpperTheory.Cb.etale_finite_presentation_model_exists n12 n17 n18

theorem n37 : LateralTheory.E.FMrangePf.IdemLift := @LateralTheory.E.IdempotentLifting.IdemLift_of

theorem n36 : LateralTheory.E.SysFMPf.FMrange := LateralTheory.E.FMrangePfQc.FMrange_of n37

theorem n33 : LateralTheory.E.NbIsoPf.SysFM := LateralTheory.E.SysFMPfSys.SysFM_of n34 n35 n36

theorem n38 : LateralTheory.E.NbIsoPf.FlatMonoLim := @LateralTheory.E.FlatMonoLimPf.FlatMonoLim_of

theorem n32 : LateralTheory.E.SysPf.NbIso := LateralTheory.E.NbIsoPf.NbIso_of n33 n38

theorem n14 : LateralTheory.E.CompCut.Sys := LateralTheory.E.SysPf.Sys_of n15 n32

theorem n39 : LateralTheory.E.CompCut.LocAC := @LateralTheory.E.LocACPf.LocAC_of

theorem n41 : LateralTheory.E.NormACPf.Loc := @LateralTheory.E.LocPf.loc

theorem n40 : LateralTheory.E.CompCut.NormAC := @LateralTheory.E.NormACPf.NormAC_of @n41

theorem n13 : LateralTheory.E.BuildCut.Comp := LateralTheory.E.CompCut.goal_of n14 n39 n40

theorem n10 : LateralTheory.E.CoverCut.Build := LateralTheory.E.BuildCut.goal_of n11 n12 n13

theorem n43 : LateralTheory.E.ProEqvPf.StageB := @LateralTheory.E.StageBPf.StageB_of

theorem n44 : LateralTheory.E.ProEqvPf.Glue := @LateralTheory.E.GluePf.glue_of

theorem n42 : LateralTheory.E.CoverCut.ProEqv := @LateralTheory.E.ProEqvPf.etale_pro_equivalence_of_continuity_mayer_vietoris_lifting_stage_glue @n17 @n18 @n43 @n44

theorem n9 : LateralTheory.E.t_E2Cut.Cover := LateralTheory.E.CoverCut.goal_of n10 n42

theorem n46 : LateralTheory.E.HZeroPf.RootAIC := @LateralTheory.E.RootAICPf.RootAIC_of

theorem n48 : LateralTheory.E.ResBijPf.TwSec := @GlobalTheory.T.tateTwist_sections_locally_generated

theorem n47 : LateralTheory.E.HZeroPf.ResBij := @LateralTheory.E.ResBijPf.ResBij_of @n48

theorem n45 : LateralTheory.E.t_E2Cut.HZero := @LateralTheory.E.HZeroPf.HZero_of @n46 @n47

theorem n50 : LateralTheory.E.AICAcycPf.Step := @LateralTheory.E.StepPf.Step_of

theorem n51 : LateralTheory.E.AICAcycPf.Cov := @LateralTheory.E.CovPf.Cov_of

theorem n49 : LateralTheory.E.t_E2Cut.AICAcyc := @LateralTheory.E.AICAcycPf.AICAcyc_of @n45 @n18 @n50 @n51

theorem n56 : LateralTheory.E.GeometricData.TopInt := @LateralTheory.E.GeometricData.topInt

theorem n60 : LateralTheory.E.LZHensFinitePf.HensIdemLift := @LateralTheory.E.LZHensFinitePf.hensIdemLift

theorem n59 : LateralTheory.E.LZProperCut.LZHensFinite := @LateralTheory.E.LZHensFinitePf.LZHensFinite_of_lift @n60

theorem n58 : LateralTheory.E.ProjectiveLineCharts₂.ProjectiveLineTwoAffineChartsPolynomialGenerated := @UpperTheory.Cb.projectiveLineCharts_of_henselianFinite @n59

theorem n61 : LateralTheory.E.ProjectiveLineCharts₂.ChartBC := @LateralTheory.E.ChartBC_nnmPf.ChartBC_of

theorem n57 : LateralTheory.E.GeometricData.LineOpens := @LateralTheory.E.ProjectiveLineCharts₂.LineOpens_of @n58 @n61

theorem n62 : LateralTheory.E.GeometricData.EmbedNonDeg := @LateralTheory.E.EmbedNonDeg₂.EmbedNonDeg_of

theorem n63 : LateralTheory.E.GeometricData.EmbedAffine := @LateralTheory.E.GeometricData.embedAffine

theorem n55 : LateralTheory.E.ChartsGeom_vpaPf.GeoData := @LateralTheory.E.GeometricData.GeoData_of @n56 @n57 @n62 @n63

theorem n65 : LateralTheory.E.ChartsGeom_vpaPf.Overlap := @LateralTheory.E.ChartOverlap₂.Overlap_of

theorem n64 : LateralTheory.E.ChartsGeom_vpaPf.CoverOfData := @LateralTheory.E.ChartsGeom_vpaPf.coverOfData_of @n65

theorem n54 : LateralTheory.E.StdChartsProof.ChartsGeom := @LateralTheory.E.ChartsGeom_vpaPf.ChartsGeom_of' @n55 @n64

theorem n66 : LateralTheory.E.StdChartsProof.FibreIdem := @UpperTheory.Cb.finite_over_henselian_fibre_idempotents_lift @n59

theorem n53 : LateralTheory.E.StandardEtaleChartsIdempotentGluing.StdCharts := @LateralTheory.E.StdChartsProof.StdCharts_of @n54 @n66

theorem n70 : LateralTheory.E.LZIdemSumNoetherian.NoetherianLocalChartOverlapFiniteComplement := @LateralTheory.E.NoetherianChartOverlapFiniteComplement.noetherian_local_chart_overlap_finite_complement

theorem n71 : LateralTheory.E.LZIdemSumNoetherian.LZIdemPow := @LateralTheory.E.LZIdemPowProof.LZIdemPow_of

theorem n72 : LateralTheory.E.LZIdemSumNoetherian.LZARStep := @LateralTheory.E.LZARFacts.LZARStep_of

theorem n69 : LateralTheory.E.IdempotentLiftingAlt.LZIdemSumNoeth := @LateralTheory.E.LZIdemSumNoetherian.goal_of @n70 @n71 @n72

theorem n73 : LateralTheory.E.IdempotentLiftingAlt.LZIdemSumApprox := @LateralTheory.E.LZIdemSumApproxYDDUPf.LZIdemSumApprox_of

theorem n68 : LateralTheory.E.StandardEtaleChartsIdempotentGluing.IdemLift := @LateralTheory.E.IdempotentLiftingAlt.IdemLift_of @n69 @n73

theorem n67 : LateralTheory.E.StandardEtaleChartsIdempotentGluing.AlgGlue := @LateralTheory.E.AlgGlue₂.AlgGlue_of @n68 @n59

theorem n52 : LateralTheory.E.t_E2Cut.LineZero := @LateralTheory.E.StandardEtaleChartsIdempotentGluing.goal_of @n53 @n67

theorem n75 : LateralTheory.E.StandardEtaleChartsMultivariableHensel.StdCharts := @LateralTheory.E.StdChartsProof₂.StdCharts_of

theorem n76 : LateralTheory.E.LineOneCut.FibCover := @LateralTheory.E.FiberCover.FibCover_of

theorem n81 : LateralTheory.E.BinPf.DescEqv := @LateralTheory.E.BinPf.DescEqv_of

theorem n80 : LateralTheory.E.ProdAcycPf.Bin := @LateralTheory.E.BinPfChains.bin_of @n81

theorem n79 : LateralTheory.E.QuotAcycCut.ProdAcyc := @LateralTheory.E.ProdAcycPf.prod_of @n80

theorem n83 : LateralTheory.E.HensCut.LocAIC := @LateralTheory.E.LocalizationIntegralClosure.LocAIC_of

theorem n84 : LateralTheory.E.HensCut.MonicSplits := @LateralTheory.E.MonicSplitsPf.MonicSplits_of

theorem n85 : LateralTheory.E.HensCut.IdemPart := @LateralTheory.E.IdemPartPf.IdemPart_of

theorem n86 : LateralTheory.E.HensCut.ColimHens := @LateralTheory.E.ColimHensPf.ColimHens_of

theorem n88 : LateralTheory.E.PartDiagCut.PartDirected := @LateralTheory.E.PartDirectedPf.PartDirected_of

theorem n89 : LateralTheory.E.PartDiagCut.DiagId := @LateralTheory.E.DiagIdPf.DiagId_of

theorem n90 : LateralTheory.E.PartDiagCut.DiagComp := @LateralTheory.E.DiagCompPf.DiagComp_of

theorem n91 : LateralTheory.E.PartDiagCut.DiagNat := @LateralTheory.E.DiagNatPf.DiagNat_of

theorem n92 : LateralTheory.E.PartDiagCut.StageProd := @LateralTheory.E.StageProdPf.StageProd_of @n83

theorem n93 : LateralTheory.E.PartDiagCut.PartA := @LateralTheory.E.PartAPf.PartA_of

theorem n94 : LateralTheory.E.PartDiagCut.PartB := @LateralTheory.E.PartBPf.PartB_of

theorem n96 : LateralTheory.E.PartCPf.Lift := @LateralTheory.E.LiftPf.Lift_of

theorem n95 : LateralTheory.E.PartDiagCut.PartC := @LateralTheory.E.PartCPfSplit.PartC_of @n83 @n84 @n85 @n93 @n96

theorem n87 : LateralTheory.E.HensCut.PartDiag := @LateralTheory.E.PartDiagCut.goal_of @n88 @n89 @n90 @n91 @n92 @n93 @n94 @n95

theorem n82 : LateralTheory.E.QuotAcycCut.Hens := @LateralTheory.E.HensCut.goal_of @n83 @n84 @n85 @n86 @n87

theorem n78 : LateralTheory.E.t_E2Cut.QuotAcyc := @LateralTheory.E.QuotAcycCut.goal_of @n79 @n82

theorem n77 : LateralTheory.E.LineOneCut.ChartAcyc := @LateralTheory.E.ChartAcycPf.ChartAcyc_of @n78

theorem n97 : LateralTheory.E.ChartSurjCut.Root := @LateralTheory.E.RootPf.Root_of

theorem multiplicative_root_pow_etale : LateralTheory.E.MulPf.RootPow := @LateralTheory.E.RootPowPf.RootPow_of

theorem multiplicative_generator_etale : LateralTheory.E.MulPf.Gen := @LateralTheory.E.GenPf.Gen_of @multiplicative_root_pow_etale

theorem multiplicative_local_generator_etale : LateralTheory.E.MulPf.LocGen := @LateralTheory.E.MulPf.LocGen_of @multiplicative_root_pow_etale

theorem twist_trivial_multiplicative : LateralTheory.E.TwistTrivial.Mul := @LateralTheory.E.MulPf.Mul_of @multiplicative_generator_etale @multiplicative_local_generator_etale

theorem locally_constant_iso_twist_trivial : LateralTheory.E.LCIsoPf.TwTriv := @LateralTheory.E.TwistTrivial.TwTriv_of @twist_trivial_multiplicative

theorem augmentation_bijective_separable : LateralTheory.E.AugBijPf.Sep := @LateralTheory.E.AugBijPf.Sep_holds

theorem augmentation_bijective_of_local_pieces : LateralTheory.E.AugBijPf.Glue := @LateralTheory.E.AugBijPf.Glue_holds

theorem augmentation_bijective_at_strictly_henselian_root : LateralTheory.E.AugBijPf.Root := @UpperTheory.Cb.augmentation_map_bijective

theorem augmentation_surjective_on_local_sections : LateralTheory.E.AugBijPf.LocSurj := @LateralTheory.E.AugBijPf.LocSurj_of @augmentation_bijective_at_strictly_henselian_root

theorem sections_localization_augmentation_compat : LateralTheory.E.AugBijPf.SecLoc := @LateralTheory.E.AugBijPf.secLoc'

theorem augmentation_localization_pow_compat : LateralTheory.E.AugBijPf.LocPow := @LateralTheory.E.LocPowPf.LocPow_of

theorem augmentation_zariski_localization_pow_compat : LateralTheory.E.AugBijPf.ZarPow := @LateralTheory.E.AugBijPf.ZarPow_of @augmentation_localization_pow_compat

theorem augmentation_generic_point_eq : LateralTheory.E.AugBijPf.GenEq := @LateralTheory.E.AugBijPf.GenEq_of @augmentation_zariski_localization_pow_compat

theorem augmentation_injective_on_local_sections : LateralTheory.E.AugBijPf.LocInj := @LateralTheory.E.AugBijPf.LocInj_of @augmentation_bijective_at_strictly_henselian_root @sections_localization_augmentation_compat @augmentation_generic_point_eq

theorem untwisted_pushforward_of_augmentation_bijective : LateralTheory.E.TateTwistZeroAugmentationBijective.AugBij := @LateralTheory.E.AugBijPf.AugBij_of_loc @augmentation_bijective_separable @augmentation_bijective_of_local_pieces @augmentation_surjective_on_local_sections @augmentation_injective_on_local_sections

theorem untwisted_pushforward_of_localized_cohomology_iso : LateralTheory.E.LCIsoPf.Tw0 := @LateralTheory.E.TateTwistZeroAugmentationSheaf.Tw0_of @untwisted_pushforward_of_augmentation_bijective

theorem secIso : LateralTheory.E.LCIsoPf.SecIso := @LateralTheory.E.LCIsoPf.SecIso_of @locally_constant_iso_twist_trivial @untwisted_pushforward_of_localized_cohomology_iso

theorem n98 : LateralTheory.E.ChartSurjCut.LCIso := @LateralTheory.E.LCIsoPf.SecIso_LCIso @secIso

theorem proper_base_change_affine_line_of_stalk_iso : LateralTheory.E.StandardEtaleChartsMultivariableHensel.Heart := @UpperTheory.cohomology_punctured_affine_line

theorem n74 : LateralTheory.E.t_E2Cut.LineOne := @LateralTheory.E.StandardEtaleChartsMultivariableHensel.goal_of @n18 @n75 @n76 @n77 @n97 @n98 @proper_base_change_affine_line_of_stalk_iso

theorem higher_affine_space_zariski_cover : LateralTheory.E.LineHighPf.ZCov := @LateralTheory.E.ZCovPf.projectiveLine_integers_affine_cover_absolutely_integrally_closed

theorem higher_affine_space_fibrewise_cover : LateralTheory.E.LineHighPf.FibCov := @LateralTheory.E.FibCovPf.FibCov_of

theorem higher_affine_space_cover_by_lines : LateralTheory.E.LineHighPf.Cover2 := @LateralTheory.E.LineHighPf.Cover2_of @higher_affine_space_zariski_cover @higher_affine_space_fibrewise_cover

theorem proper_base_change_affine_space : LateralTheory.E.t_E2Cut.LineHigh := @LateralTheory.E.LineHighPf.LineHigh_of @n78 @n18 @higher_affine_space_cover_by_lines

theorem integral_pullback_henselian_lift : LateralTheory.E.IntPBPf.IntHens := @LateralTheory.E.IntHensPf.IntHens_of

theorem integral_pullback_fibre_iso : LateralTheory.E.IntPBPf.IntFib := @LateralTheory.E.IntFibPf.IntFib_of

theorem proper_base_change_integral_pullback : LateralTheory.E.t_E2Cut.IntPB := @LateralTheory.E.IntPBPf.IntPB_of @integral_pullback_henselian_lift @integral_pullback_fibre_iso

theorem stein_factorization_relative_normalization : LateralTheory.E.SteinPf.RelNorm := @LateralTheory.E.RelNormPf.RelNorm_of

theorem stein_factorization_integral_closure_open : LateralTheory.E.SteinPf.AICOpen := @LateralTheory.E.AICOpenPf.AICOpen_of

theorem proper_base_change_stein_factorization : LateralTheory.E.t_E2Cut.Stein := LateralTheory.E.SteinPf.Stein_of stein_factorization_relative_normalization stein_factorization_integral_closure_open

theorem stalk_pushforward_continuous_limit : LateralTheory.E.StalkGermPf.StalkCont := @LateralTheory.E.StalkContPf.StalkCont_of

theorem stalk_eq_germ_of_zariski_local : LateralTheory.E.ZLGPf.StalkGerm := @LateralTheory.E.StalkGermPf.StalkGerm_of @stalk_pushforward_continuous_limit

theorem zariski_induction_injective_mayer_vietoris : LateralTheory.E.InjStepPf.OverMV := @LateralTheory.E.OverMVPf.OverMV_of

theorem zariski_induction_injective_two_open_cover : LateralTheory.E.InjStepPf.TwoStep := @LateralTheory.E.InjStepPf.TwoStep_of @zariski_induction_injective_mayer_vietoris

theorem zariski_induction_empty_cohomology : LateralTheory.E.InjStepPf.EmptyH := @LateralTheory.E.EmptyH₂.EmptyH_of

theorem zariski_induction_injectivity_of_etale_comparison : LateralTheory.E.ZarIndPf.InjStep := @LateralTheory.E.InjStepPf.InjStep_of @zariski_induction_injective_two_open_cover @zariski_induction_empty_cohomology

theorem zariski_induction_surjectivity_of_etale_comparison : LateralTheory.E.ZarIndPf.SurjStep := @LateralTheory.E.SurjStepPf.SurjStep_of

theorem zariski_induction_step_bijective : LateralTheory.E.ZarIndPf.Step := @LateralTheory.E.ZarIndPf.Step_of @zariski_induction_injectivity_of_etale_comparison @zariski_induction_surjectivity_of_etale_comparison

theorem zariski_local_to_global_induction : LateralTheory.E.ZLGPf.ZarInd := @LateralTheory.E.ZarIndPf.ZarInd_of_step @zariski_induction_step_bijective

theorem proper_base_change_zariski_local_to_global : LateralTheory.E.t_E2Cut.ZLG := @LateralTheory.E.ZLGPf.ZLG_of @n17 @n18 @stalk_eq_germ_of_zariski_local @zariski_local_to_global_induction

theorem fibre_closed_quasi_compact_quasi_separated : LateralTheory.E.FibClosedPf.FibQCQS := @LateralTheory.E.FibClosedPf.fibQCQS

theorem fibre_stalk_absolutely_integrally_closed : LateralTheory.E.FibStalkPf.StalkAIC := @LateralTheory.E.StalkSHSPf.stalkAIC

theorem fibre_stalk_strictly_henselian_sep_closed : LateralTheory.E.FibStalkPf.StalkSHS := @LateralTheory.E.FibStalkPf.stalkSHS_of @fibre_stalk_absolutely_integrally_closed

theorem strictly_henselian_quotient : LateralTheory.E.FibStalkPf.QuotSH := @LateralTheory.E.FibStalkPf.quotSH

theorem fibre_stalk_strictly_henselian : LateralTheory.E.FibStalkPf.StalkSH := @LateralTheory.E.FibStalkPf.StalkSH_of @fibre_stalk_strictly_henselian_sep_closed @strictly_henselian_quotient

theorem base_absolutely_integrally_closed_integral : LateralTheory.E.BaseAICPf.BaseInt := @LateralTheory.E.BaseIntPf.BaseInt_of

theorem base_absolutely_integrally_closed_localization_localization : LateralTheory.E.BaseAICPf.BaseLocLoc := @LateralTheory.E.BaseLocLocPf.BaseLocLoc_of

theorem base_absolutely_integrally_closed_localization : LateralTheory.E.BaseAICPf.BaseLoc := LateralTheory.E.BaseAICPf.BaseLoc_of base_absolutely_integrally_closed_localization_localization

theorem fibre_equivalence_base_absolutely_integrally_closed : LateralTheory.E.FibreEqvPf.BaseAIC := LateralTheory.E.BaseAICPf.BaseAIC_of base_absolutely_integrally_closed_integral base_absolutely_integrally_closed_localization

theorem stalk_ring_absolutely_integrally_closed : LateralTheory.E.FibreEqvPf.StalkAICRing := @LateralTheory.E.StalkAICRingPf.StalkAICRing_of

theorem spec_absolutely_integrally_closed_cohomology : LateralTheory.E.FibreEqvPf.SpecAIC := @LateralTheory.E.SpecAICPf.SpecAIC_of

theorem fibre_equivalence_stalk_absolutely_integrally_closed : LateralTheory.E.FibreEqvPf.StalkAIC := @LateralTheory.E.FibreEqvPf.StalkAIC_of @stalk_ring_absolutely_integrally_closed @spec_absolutely_integrally_closed_cohomology

theorem fibre_equivalence_stalk_fibre : LateralTheory.E.FibreEqvPf.StalkFib := LateralTheory.E.FibreEqvPf.StalkFib_of fibre_equivalence_base_absolutely_integrally_closed fibre_equivalence_stalk_absolutely_integrally_closed

theorem fibre_stalk_equivalence : LateralTheory.E.FibStalkPf.FibreEqv := @LateralTheory.E.FibreEqvPf.FibreEqv_of @fibre_stalk_strictly_henselian_sep_closed @fibre_equivalence_stalk_fibre

theorem closed_fibre_stalk_cohomology : LateralTheory.E.FibClosedPf.FibStalk := @LateralTheory.E.FibStalkPf.FibStalk_of @fibre_stalk_strictly_henselian @fibre_stalk_equivalence

theorem proper_base_change_closed_fibre : LateralTheory.E.FibPf.FibClosed := @LateralTheory.E.FibClosedPf.FibClosed_of @proper_base_change_zariski_local_to_global @n45 @n49 @fibre_closed_quasi_compact_quasi_separated @closed_fibre_stalk_cohomology

theorem proper_base_change_fibre : LateralTheory.E.t_E2Cut.Fib := @LateralTheory.E.FibPf.Fib_of @proper_base_change_closed_fibre @n45 @n49

theorem chow_lemma_image : LateralTheory.E.ChowCut.Img := @LateralTheory.E.ImgPf.Img_of

theorem chow_lemma_iterated_base_change : LateralTheory.E.ChowLCut.IterBC := @LateralTheory.E.IterBCPf.IterBC_of

theorem chow_graph_open_cover : LateralTheory.E.ChowGraphCut.Cover := @LateralTheory.E.CoverExistence.Cover_of

theorem embedding_affine_closed_immersion : LateralTheory.E.EmbedPf.AffClosed := @LateralTheory.E.EmbedPf.affClosed

theorem chow_lemma_projective_line_extension : LateralTheory.E.ChowLCut.LineEx := @LateralTheory.E.LineExPf.LineEx_of

theorem embedding_projective_line_chart : LateralTheory.E.EmbedPf.LineChart := @LateralTheory.E.LineChartPf.LineChart_of

theorem embedding_affine_chart : LateralTheory.E.EmbedPf.Chart := LateralTheory.E.EmbedPf.chart_of chow_lemma_projective_line_extension embedding_projective_line_chart

theorem chow_graph_projective_embedding : LateralTheory.E.ChowGraphCut.Embed := @LateralTheory.E.EmbedPf.Embed_of @embedding_affine_closed_immersion @embedding_affine_chart

theorem chow_graph_iterated_composition : LateralTheory.E.ChowGraphCut.IterComp := @LateralTheory.E.IterCompPf.IterComp_of

theorem chow_graph_fibre_product : LateralTheory.E.ChowGraphCut.Prod := LateralTheory.E.ProdPf.Prod_of chow_graph_iterated_composition

theorem chow_graph_projective_reduction : LateralTheory.E.ChowGraphCut.Core := @LateralTheory.E.ImageInPf.Core_of

theorem chow_lemma_graph_construction : LateralTheory.E.ChowLCut.ChowGraph := LateralTheory.E.ChowGraphCut.goal_of chow_graph_open_cover chow_graph_projective_embedding chow_graph_fibre_product chow_graph_projective_reduction

theorem chow_lemma_projective_cover : LateralTheory.E.ChowCut.ChowL := LateralTheory.E.ChowLCut.goal_of chow_lemma_iterated_base_change chow_lemma_graph_construction

theorem normalization_affine_absolutely_integrally_closed : LateralTheory.E.NormPf.AICPf.AffAIC := @LateralTheory.E.NormPf.AffPf.affAIC

theorem normalization_local_absolutely_integrally_closed : LateralTheory.E.NormPf.AICPf.LocAIC := @LateralTheory.E.LocalIntegralClosureRoots.LocAIC_of

theorem chow_lemma_normalization : LateralTheory.E.ChowCut.Norm := @LateralTheory.E.NormPf.AICPf.norm_full @normalization_affine_absolutely_integrally_closed @normalization_local_absolutely_integrally_closed

theorem e2Cut_chow : LateralTheory.E.t_E2Cut.Chow := LateralTheory.E.ChowCut.goal_of chow_lemma_image chow_lemma_projective_cover chow_lemma_normalization

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut in

theorem towers (H : Hyp) (q : ℕ) (i : ℤ) (B : Type) [CommRing B] [IsLocalRing B] (hB : SH B) (hq : IsUnit (q : B))
    {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of B)) (hr : IT r) : PB q i r := by
  have h := tower H n1 n9 n45 n49 n52 n74 proper_base_change_affine_space proper_base_change_integral_pullback proper_base_change_stein_factorization proper_base_change_fibre q i B hB hq r hr (𝟙 Y) inferInstance
  simpa using h

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut in

theorem main (H : Hyp) : E2 := by
  intro q A _ _ hA hq X p _ i
  show PB q i p
  refine reduce H n1 n9 q i A hq p ?_
  intro Z h hh hZ
  obtain ⟨Z', c, hZ', hdom, hc, hcomp⟩ := e2Cut_chow A h p hh hZ
  obtain ⟨hcqc, hcqs⟩ := IT.qc hc
  have hT : PB q i (c ≫ h ≫ p) := towers H q i A hA hq (c ≫ h ≫ p) hcomp
  refine (proper_base_change_fibre H q i A hq c (h ≫ p) hZ' hZ ?_).1 hT
  intro B _ _ hB hqB t
  exact towers H q i B hB hqB (pullback.snd c t) (IT.bc hc t (IsPullback.of_hasPullback c t))

end UpperTheory.Et.E2
