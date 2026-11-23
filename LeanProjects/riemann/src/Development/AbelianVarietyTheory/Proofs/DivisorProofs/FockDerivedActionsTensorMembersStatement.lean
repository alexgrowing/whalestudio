import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembers
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_derived_actions_tensor_members : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), Continuous F.emb ∧ (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => F.π (T1.expt (t • Y), 1) (F.ι P)) (F.ι (fockAct1 p q r s Y P)) 0) ∧ (∀ Y ∈ upq r s, ∀ P, HasDerivAt (fun t : ℝ => F.π (1, T2.expt (t • Y)) (F.ι P)) (F.ι (fockAct2 p q r s Y P)) 0) := by
  first | exact @GlobalTheory.FockEmbExp.fock_derived | exact GlobalTheory.FockEmbExp.fock_derived | (intros; apply GlobalTheory.FockEmbExp.fock_derived <;> assumption)
