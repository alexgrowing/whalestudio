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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayFromPlacesBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSumDenominatorBoundOfFactorClaims
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOfSumBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryBoundOfInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDataBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGammaBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteFormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePairBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRowOfDictionaryDepthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTopOfDictionaryDepthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteClassBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteCountOfDepthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSumSizeBoundLargeDataFromFactorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteRowOfDictionaryDepthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTensorBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTopOfDictionaryDepthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteScalarBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement

namespace GlobalTheory.SumSize.Join

theorem fin_away_inf : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.SumSize.FinK ∧ GlobalTheory.SumSize.AwayK ∧ GlobalTheory.SumSize.InfK := by
  intro P
  have hInp : ∀ D, GlobalTheory.NormSum.Inp D := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied
  have hOK : GlobalTheory.RowClaim.SumOKK := GlobalTheory.T.row_sum_of_published_inputs P
  have hDep : GlobalTheory.SumSize.DepthK := GlobalTheory.T.depth_of_sum_bound P hOK
  have hDict : GlobalTheory.SumSize.DictK := GlobalTheory.T.dictionary_bound_of_inputs P hInp
  have hScal := GlobalTheory.T.finite_infinite_scalar_bounds P
  have hForm := GlobalTheory.T.finite_infinite_form_bounds P
  have hPair := GlobalTheory.T.finite_infinite_pair_bounds P
  have hPsi := GlobalTheory.Adopt.finite_infinite_psi_bounds P
  have hTopF := GlobalTheory.T.finite_top_of_dictionary_depth P hInp hDict hDep
  have hRowF := GlobalTheory.T.finite_row_of_dictionary_depth P hInp hDict hDep
  have hTopI := GlobalTheory.T.infinite_top_of_dictionary_depth P hInp hDict hDep
  have hRowI := GlobalTheory.T.infinite_row_of_dictionary_depth P hInp hDict hDep
  refine ⟨?_, GlobalTheory.Adopt.away_from_places_bound P, ?_⟩
  · exact GlobalTheory.Adopt.finiteSumDenominatorBound_of_factor_claims hOK hDep hScal.1 (GlobalTheory.Adopt.finite_coefficient_bound P) (GlobalTheory.T.finite_data_bound P) (GlobalTheory.T.finite_gamma_bound P)
      hTopF hRowF hPair.1 hPsi.1 hForm.1
  · exact GlobalTheory.T.archimedeanSumSizeBound_largeData_from_factors hOK hDep hScal.2 (GlobalTheory.T.infinite_tensor_bound P) (GlobalTheory.T.infinite_count_of_depth P hDep) (GlobalTheory.T.infinite_class_bound P)
      hTopI hRowI hPair.2 hPsi.2 hForm.2

end GlobalTheory.SumSize.Join
