import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyTwoInstances
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joinedMapsAgreeCohomologyTwo_instances : JoinedTwo.{1,1} ∧ JoinedTwo.{1,0} ∧ JoinedTwo.{0,0} := by
  first | exact @GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst | exact GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst | (intros; apply GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst <;> assumption)
