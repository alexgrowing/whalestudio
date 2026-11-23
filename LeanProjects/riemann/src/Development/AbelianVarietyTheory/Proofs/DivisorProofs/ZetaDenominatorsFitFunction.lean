import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaJetClassSumArchimedeanBoundOfCmTheta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassSumDenominatorBoundOfCmThetaHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivLOneBoundFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioConjugatesOfTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFamilyEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFittedIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleOfRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorFittedIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsFifthEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsSeventhEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDataExistenceOfSumsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityFittedIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePartIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaLowGivesFirstIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelAtFittedPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityAtFittedPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAtFittedPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSquareFittedIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingFunctionBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBoundFittedIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTopStatementsOfInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSizeFiniteAwayInfiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRowStatementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioInEmbeddingRangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHoldsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsCuspidalOfFunctorialityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvKWithRealAll

open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun.Close

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cloudIcc {D : D7} (L : SizeData₂ D) (τ i : ℕ) :
    0 ≤ cloud D τ i ∧ (cloud D τ i : ℝ) ≤ L.Sc := by
  unfold cloud
  split_ifs with h
  · dsimp only [GlobalTheory.SignedHC.GridData.ofHCParam]
    unfold GlobalTheory.SignedHC.GridData.extend
    split_ifs with h2
    · obtain ⟨h0, h1⟩ := L.cloud_v ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩) ⟨i - 2, h2⟩
      refine ⟨Int.floor_nonneg.mpr (by exact_mod_cast h0), ?_⟩
      have hf := Int.floor_le ((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩)
      have hf' : (((⌊(D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩⌋ : ℤ) : ℚ) : ℝ) ≤
          (((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩ : ℚ) : ℝ) := by exact_mod_cast hf
      push_cast at hf' ⊢
      linarith
    · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩
  · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩

theorem lcLeOfCloud {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) (S : ℝ) (h0 : 0 ≤ S) (hcl : ∀ τ i, 0 ≤ O.cl τ i ∧ (O.cl τ i : ℝ) ≤ S) :
    (O.Lc : ℝ) ≤ S := by
  have hL : O.Lc ≤ ⌊S⌋₊ := by
    unfold FunData.Lc
    refine Finset.sup_le fun τ _ => ?_
    rw [Nat.le_floor_iff h0]
    obtain ⟨a0, a1⟩ := hcl τ 2
    obtain ⟨b0, -⟩ := hcl τ O.k
    have h : ((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) ≤ O.cl τ 2 := by omega
    have h' : (((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) : ℝ) ≤ ((O.cl τ 2 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc (O.Lc : ℝ) ≤ (⌊S⌋₊ : ℝ) := by exact_mod_cast hL
    _ ≤ S := Nat.floor_le h0

theorem scLeB {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : L.Sc ≤ L.sc.b := by
  have hk := P.kS_le
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hn : (1 : ℝ) ≤ D.R.n := by
    unfold Ranks.n
    exact_mod_cast (show 1 ≤ D.R.ord from D.R.ord_pos)
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hw : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w'' Scale.b' Scale.a
    rw [div_le_iff₀ (by positivity)]
    calc L.sc.x * L.sc.b / L.sc.X' ≤ L.sc.x * L.sc.b := div_le_self (by positivity) hX
      _ ≤ L.sc.b * (L.sc.x * D.R.n) := by nlinarith [mul_nonneg (mul_pos hx hb).le (sub_nonneg.2 hn)]
  have hS := L.Sc_pos
  nlinarith

theorem desHLeaf : DesH := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps heps _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩⟩
  intro _
  refine ⟨0, fun C _ => ?_⟩
  have hW : PageWin Fm := hF.2.1
  refine ⟨max (Fm.x1 + 1) ((8 : ℝ) ^ (1 / eps)), fun x hx hx0 i p _ d _ => ?_⟩
  have hx1 : 1 < x := lt_trans Fm.one_lt_family_threshold hx
  have hx0' : (0 : ℝ) < x := by linarith
  have h8 : (8 : ℝ) ≤ x ^ (8 * eps) := by
    have e1 : (8 : ℝ) = ((8 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ heps.ne', Real.rpow_one]
    have e2 : ((8 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps :=
      Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx0) heps.le
    have e3 : x ^ eps ≤ x ^ (8 * eps) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  obtain ⟨⟨hn, -⟩, ⟨-, hm⟩, -⟩ := hW x hx i
  have hδ : (Fm.L x i).sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos (Fm.L x i).sc.one_lt_alt.le
      (by linarith [(Fm.L x i).sc.eps_pos])
  have hδ0 : 0 ≤ (Fm.L x i).sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hm4 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ (((Fm.D x i).R.f : ℕ) : ℝ) := by
    have hs := Real.sq_sqrt (mul_nonneg hx0'.le hδ0)
    have hs0 := Real.sqrt_nonneg (x * (Fm.L x i).sc.delta1)
    have hm0 : (0 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by positivity
    have hm2 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 2 ≤ 4 * x := by nlinarith
    have hm4' : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ 16 * x ^ 2 := by nlinarith
    have hpow : x ^ ((2 : ℝ) + 8 * eps) = x ^ 2 * x ^ (8 * eps) := by
      rw [Real.rpow_add hx0', Real.rpow_two]
    have hf : (((Fm.D x i).R.f : ℕ) : ℝ) = 2 * ((Fm.D x i).R.n : ℝ) := by
      unfold Ranks.f
      push_cast
      ring
    rw [hf]
    have hx2 : 0 ≤ x ^ 2 := by positivity
    nlinarith
  refine ⟨⟨(Fm.D x i).R.two_le_m, (Fm.D x i).R.m_add_three_le_k, by exact_mod_cast hm4,
    (Fm.D x i).R.f_le_k⟩, ?_⟩
  show (FunData.Lc d.O : ℝ) ≤ (Fm.L x i).sc.b
  exact (lcLeOfCloud d.O (Fm.L x i).Sc (Fm.L x i).Sc_pos.le
    (fun τ j => cloudIcc (Fm.L x i) τ j)).trans (scLeB (Fm.params x hx i))

theorem fun0Fit_close : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator →
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.ToricTransport.TwistedTransport → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.SqTop.Refl →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate →
    GlobalTheory.BigTop.LamLow → GlobalTheory.BigTop.Fun.Fun0Fit @GlobalTheory.BigTop.Fun.Fld := by
  intro hP hH hTD hTr hTw hZ hR hAg hMa hFS hL
  obtain ⟨hDenSum, hThbSt, hOneSqSt, hBotSmall, hBotNe, hFieldDat, hTorEx, hDenEx, hBotEx, hLNe, hTriEx, hTower⟩ :=
    GlobalTheory.T.square_top_statements_of_inputs hP.howeDualityReal hP hH hTD hTr hZ hR hAg hMa
  obtain ⟨hFin, hAway, hInf⟩ := GlobalTheory.T.sum_size_finite_away_infinite hP
  obtain ⟨hSumOK, hConst, hLin, hF2, hSumRat⟩ := GlobalTheory.T.theta_integral_row_statements hP hAg hMa
  have hInj := GlobalTheory.RowTest.injK_of_separates hFS (GlobalTheory.RowTest.convK_withReal_all hP (GlobalTheory.T.lifts_cuspidal_of_functoriality hP))
  have hSize := GlobalTheory.T.size_at_holds
  have hSet := GlobalTheory.T.set_at_of_size_at hSize
  have hDl := GlobalTheory.T.log_deriv_L_one_bound_family hP
  have hInp := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied
  have hIntSt := GlobalTheory.T.classSumDenominatorBound_of_cmThetaHypotheses hInp
  have hArchSt := GlobalTheory.ArchTop.archSt_of_inp hInp
  have hThA := GlobalTheory.T.toric_ratio_family_estimate (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport hTw) hSet hDl hFieldDat hTorEx
  have hSq := GlobalTheory.T.square_ratio_in_embedding_range hP hAg hMa hSet hDl hConst hLNe hTriEx hTower
  have hB : Bundle := @GlobalTheory.BigTop.Fun.bundle_of_rows
  exact GlobalTheory.BigTop.Fun.fun0Fit_of_leaves _ _ hB GlobalTheory.T.scaling_function_bound
    (GlobalTheory.T.field_data_existence_of_sums hSet hDl hSumOK hSumRat hConst hSq hIntSt hFieldDat hTorEx hDenEx hBotEx hBotSmall)
    (GlobalTheory.T.multiplicity_at_fitted_points hSet) (GlobalTheory.T.one_map_at_fitted_points hB hSet hLin hInj hConst hF2) (GlobalTheory.T.kernel_at_fitted_points hB hSet hLin hInj hConst hF2)
    (GlobalTheory.T.finite_and_away_formula hSet hFin hAway) (GlobalTheory.T.infinite_part_identity hB hSet hInf) (GlobalTheory.T.lambda_low_gives_first_identity hL)
    (GlobalTheory.T.one_square_fitted_identity hSet hDl hThA hOneSqSt) (GlobalTheory.T.denominator_fitted_identity hSet hDl hDenSum) (GlobalTheory.T.integrality_fitted_identity hSet hDl hBotSmall hBotNe)
    (GlobalTheory.T.archimedean_fitted_identity hSet hDl hArchSt hBotSmall) (GlobalTheory.T.theta_bound_fitted_identity hSet hDl hThbSt) (GlobalTheory.T.weight_of_size_bound hSize)
    desHLeaf GlobalTheory.T.rank_gap_bound' GlobalTheory.T.ramified_sum_bound GlobalTheory.T.polynomial_descent_estimate

end GlobalTheory.BigTop.Fun.Close
