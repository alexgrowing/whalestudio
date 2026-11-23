import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSizeFiniteAwayInfinite
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RowSumOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DepthOfSumBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeDictionaryOfLocalBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteInfiniteScalarBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FormValueFiniteInfiniteFactorization
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FieldPairComparison
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TestVectorValueFactorization
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteTopTermIntegralBoundOfLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeBoundFinitePlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KernelConjugationMeanArchimedeanTopTerm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanSumSizeOppositeConjugate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLocalFactorAwayFromLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteCoefficientBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteDataBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GammaFactorLossAtFinitePlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanTensorSizeBoundOfLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanSumCountBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanClassCountBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSizeFiniteAwayInfiniteStatement

section
namespace GlobalTheory.SumSize.Join
theorem sum_size_finite_away_archimedean_combined : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SumSize.FinK ∧ GlobalTheory.SumSize.AwayK ∧ GlobalTheory.SumSize.InfK := by
  intro P
  have hInp : ∀ D, GlobalTheory.NormSum.Inp D := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied
  have hOK : GlobalTheory.RowClaim.SumOKK := _root_.GlobalTheory.T.sumOKK_of_theta_local_inputs P
  have hDep : GlobalTheory.SumSize.DepthK := _root_.GlobalTheory.T.depthK_of_sumOKK P hOK
  have hDict : GlobalTheory.SumSize.DictK := _root_.GlobalTheory.T.sum_size_dictionary P hInp
  have hScal := _root_.GlobalTheory.T.finite_and_infinite_scalar_bounds P
  have hForm := _root_.GlobalTheory.T.form_value_finite_infinite_factorization P
  have hPair := _root_.GlobalTheory.T.field_pair_comparison P
  have hPsi := _root_.GlobalTheory.Adopt.test_vector_value_factorization P
  have hTopF := _root_.GlobalTheory.T.sum_size_finite_top_term_integral P hInp hDict hDep
  have hRowF := _root_.GlobalTheory.T.sum_size_bound_finite_places P hInp hDict hDep
  have hTopI := _root_.GlobalTheory.T.kernel_conjugation_mean_archimedean_top_term P hInp hDict hDep
  have hRowI := _root_.GlobalTheory.T.sum_size_bound_opposite_conjugation P hInp hDict hDep
  refine ⟨?_, _root_.GlobalTheory.Adopt.twisted_local_factor_away_from_level P, ?_⟩
  · exact GlobalTheory.Adopt.finiteSumDenominatorBound_of_factor_claims hOK hDep hScal.1 (_root_.GlobalTheory.Adopt.finCoefK_of_theta_inputs P) (_root_.GlobalTheory.T.finDatK_of_theta_inputs P) (_root_.GlobalTheory.T.gamma_factor_loss_at_finite_places P)
      hTopF hRowF hPair.1 hPsi.1 hForm.1
  · exact GlobalTheory.T.archimedeanSumSizeBound_largeData_from_factors hOK hDep hScal.2 (_root_.GlobalTheory.T.sum_size_archimedean_tensor_bound P) (_root_.GlobalTheory.T.sum_count_bound_archimedean P hDep) (_root_.GlobalTheory.T.class_count_bound_archimedean P)
      hTopI hRowI hPair.2 hPsi.2 hForm.2
end GlobalTheory.SumSize.Join
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_size_bound_all_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SumSize.FinK ∧ GlobalTheory.SumSize.AwayK ∧ GlobalTheory.SumSize.InfK := by
  first | exact @_root_.GlobalTheory.SumSize.Join.sum_size_finite_away_archimedean_combined | exact _root_.GlobalTheory.SumSize.Join.sum_size_finite_away_archimedean_combined | (intros; apply _root_.GlobalTheory.SumSize.Join.sum_size_finite_away_archimedean_combined <;> assumption)
end
