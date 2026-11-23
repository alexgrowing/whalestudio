import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirCommuteSameBlockUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagonalFibreCasimir_commute_sameBlock_unit : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), IsGl F → ∀ a b, s a = s b → cas s F * F a b = F a b * cas s F := by
  first | exact @GlobalTheory.HoweR.cas_mul_comm_of_block | exact GlobalTheory.HoweR.cas_mul_comm_of_block | (intros; apply GlobalTheory.HoweR.cas_mul_comm_of_block <;> assumption)
