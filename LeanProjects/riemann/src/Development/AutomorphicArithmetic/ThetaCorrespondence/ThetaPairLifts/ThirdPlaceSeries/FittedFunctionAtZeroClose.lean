import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareTopTermJoinedEstimates
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeFiniteAwayArchimedeanCombined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JoinedLocalSumEstimates
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedConvergenceWithRealPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingOfSizeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LogDerivLFunctionAtOneLeAlongFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThmAUpperStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareRatioAtPointOfLeadingTerm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundleOfRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIntegralMultipleHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExOfClaimsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MmTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneMapOfRowsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerEqOfFormulaStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafFixedPointOfFinKAwayKStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpaTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpbOfLamLowStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneSqTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DenTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ArchTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThbTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtTieStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DesHLeaf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamifiedSumsFifthBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamifiedSumsSeventhBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DesPolStatement

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun.Close
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem fittedFunction_at_zero_close_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator →
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.ToricTransport.TwistedTransport → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.SqTop.Refl →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate →
    _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits @GlobalTheory.BigTop.Fun.Fld := by
  intro hP hH hTD hTr hTw hZ hR hAg hMa hFS hL
  obtain ⟨hDenSum, hThbSt, hOneSqSt, hBotSmall, hBotNe, hFieldDat, hTorEx, hDenEx, hBotEx, hLNe, hTriEx, hTower⟩ :=
    _root_.GlobalTheory.T.square_leading_term_bound hP.howeDualityReal hP hH hTD hTr hZ hR hAg hMa
  obtain ⟨hFin, hAway, hInf⟩ := _root_.GlobalTheory.T.sum_size_bound_all_places hP
  obtain ⟨hSumOK, hConst, hLin, hF2, hSumRat⟩ := _root_.GlobalTheory.T.local_sum_estimates_joined hP hAg hMa
  have hInj := GlobalTheory.RowTest.injK_of_separates hFS (_root_.GlobalTheory.RowTest.twisted_convergence_with_real_places hP (_root_.GlobalTheory.T.twisted_thetaLift_cuspidal hP))
  have hSize := _root_.GlobalTheory.T.size_at'
  have hSet := _root_.GlobalTheory.T.set_at_of_size_at' hSize
  have hDl := _root_.GlobalTheory.T.abs_logDerivativeAtOne_le_x_rpow_eps hP
  have hInp := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied
  have hIntSt := GlobalTheory.T.classSumDenominatorBound_of_cmThetaHypotheses hInp
  have hArchSt := GlobalTheory.ArchTop.archSt_of_inp hInp
  have hThA := _root_.GlobalTheory.T.toric_ratio_family_estimate' (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport hTw) hSet hDl hFieldDat hTorEx
  have hSq := _root_.GlobalTheory.T.sq_ratio_mem_range_emb_ll hP hAg hMa hSet hDl hConst hLNe hTriEx hTower
  have hB : _root_.GlobalTheory.BigTop.Fun.BundleCondition := @_root_.GlobalTheory.BigTop.Fun.bundle_of_rows_alt
  exact _root_.GlobalTheory.BigTop.Fun.fun0Fit_of_leaves_alt _ _ hB _root_.GlobalTheory.T.scaling_function_bound'
    (_root_.GlobalTheory.T.existsFunctionIn_of_sqRatio_range hSet hDl hSumOK hSumRat hConst hSq hIntSt hFieldDat hTorEx hDenEx hBotEx hBotSmall)
    (_root_.GlobalTheory.T.leafMinimalMass_of_setAt hSet) (_root_.GlobalTheory.T.oneMap_of_bundle_setAt_lin_inj_const_formula hB hSet hLin hInj hConst hF2) (_root_.GlobalTheory.T.leafKernel_tie_of_claim_inputs hB hSet hLin hInj hConst hF2)
    (_root_.GlobalTheory.T.leafFixedPoint_of_finK_awayK hSet hFin hAway) (_root_.GlobalTheory.T.leafHeightMapBound_of_infK hB hSet hInf) (_root_.GlobalTheory.T.leafInfinitePlaceBound_of_lamLow hL)
    (_root_.GlobalTheory.T.oneSq_of_log_derivative_bound_and_oneSqSt hSet hDl hThA hOneSqSt) (_root_.GlobalTheory.T.leafDensity_of_logDeriv_bound_and_denSum hSet hDl hDenSum) (_root_.GlobalTheory.T.leafIntegrality_of_logDeriv_bound hSet hDl hBotSmall hBotNe)
    (_root_.GlobalTheory.T.arch_tie_of_setAt_logDeriv hSet hDl hArchSt hBotSmall) (_root_.GlobalTheory.T.leaf_theta_bound_of_set_at hSet hDl hThbSt) (_root_.GlobalTheory.T.weight_of_size_bound' hSize)
    _root_.GlobalTheory.BigTop.Fun.Close.desHLeaf_alt _root_.GlobalTheory.T.rank_gap_bound _root_.GlobalTheory.T.ramified_sum_bound' _root_.GlobalTheory.T.polynomial_descent_estimate'
end GlobalTheory.BigTop.Fun.Close
end
end
end
