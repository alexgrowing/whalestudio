import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantKernelStableAndAdmissible
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCoinvariantKernel_stable_and_admissible : ∀ (P Q R S : ℕ) (x : ℂ), Stab (fockAct2 P Q R S) (coinv P Q R S x) ∧ AdmMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  first | exact @GlobalTheory.HoweR.coinv_stab_adm | exact GlobalTheory.HoweR.coinv_stab_adm | (intros; apply GlobalTheory.HoweR.coinv_stab_adm <;> assumption)
