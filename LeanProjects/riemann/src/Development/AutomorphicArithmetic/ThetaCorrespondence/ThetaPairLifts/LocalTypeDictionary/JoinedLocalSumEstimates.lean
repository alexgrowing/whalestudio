import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRowStatements
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftRowPropertiesConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRowStatementsStatement

section
namespace GlobalTheory.RowClaim.JoinF
theorem joined_local_sum_estimates :
    _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK :=
  fun hP hK hM =>
    _root_.GlobalTheory.T.thetaLift_row_properties hP hK hM (_root_.GlobalTheory.T.twisted_theta_integral_converges hP.siegelSetUnitary hP)
      (_root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM) (_root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hM)
end GlobalTheory.RowClaim.JoinF
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_sum_estimates_joined : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  first | exact @_root_.GlobalTheory.RowClaim.JoinF.joined_local_sum_estimates | exact _root_.GlobalTheory.RowClaim.JoinF.joined_local_sum_estimates | (intros; apply _root_.GlobalTheory.RowClaim.JoinF.joined_local_sum_estimates <;> assumption)
end
