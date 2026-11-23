import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyZeroOneInstances
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances : JoinedOne.{1,1} ∧ JoinedOne.{1,0} ∧ JoinedOne.{0,0} := by
  first | exact @GlobalTheory.CxCoh.joinedOne_inst | exact GlobalTheory.CxCoh.joinedOne_inst | (intros; apply GlobalTheory.CxCoh.joinedOne_inst <;> assumption)
