import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingAssembly
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConstK
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairLiftCuspidalOfHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RowSumOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedCharactersLinearlyIndependent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedPeriodIdentityLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLiftFlipInvariant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaIntegralUnfolding
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedJetSuccEqAssembly
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingAssemblyStatement

section
namespace GlobalTheory.RowClaim.Join
theorem thetaLift_row_properties_conj : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  intro P K L s1 s2 s3
  have c := _root_.GlobalTheory.ConstNZ.constK_alt P K L s1 s2 s3
  have cusp := _root_.GlobalTheory.T.twisted_thetaLift_cuspidal P
  have sum := _root_.GlobalTheory.T.sumOKK_of_theta_local_inputs P
  exact ⟨sum, c, _root_.GlobalTheory.T.twisted_characters_linearly_independent P cusp,
    GlobalTheory.T.rowTestLiftFormula_principalLevel (_root_.GlobalTheory.T.twisted_period_identity P) (_root_.GlobalTheory.T.twisted_lift_flip_invariant P cusp s1 K c) (_root_.GlobalTheory.T.twisted_theta_integral_unfolds P cusp sum)
      (_root_.GlobalTheory.T.twisted_jets_assemble P sum) c sum,
    GlobalTheory.T.rowTestRationalSums_of_finiteSumsMeaningful sum⟩
end GlobalTheory.RowClaim.Join
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_row_properties : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  first | exact @_root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj | exact _root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj | (intros; apply _root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj <;> assumption)
end
