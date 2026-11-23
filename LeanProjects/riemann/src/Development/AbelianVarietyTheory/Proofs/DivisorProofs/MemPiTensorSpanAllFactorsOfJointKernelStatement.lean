import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPiTensorSpanAllFactorsOfJointKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_piTensorSpanAllFactors_of_jointKernel : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (L : ∀ w, Set (Module.End ℂ (V w))) (H : ∀ w, Submodule ℂ (V w)), (∀ w v, (∀ l ∈ L w, l v = 0) → v ∈ H w) → ∀ y : PiTensorProduct ℂ V, (∀ w, ∀ l ∈ L w, atPl w l y = 0) → y ∈ tensAll H := by
  first | exact @GlobalTheory.HoweR.mem_tensAll_of_killed | exact GlobalTheory.HoweR.mem_tensAll_of_killed | (intros; apply GlobalTheory.HoweR.mem_tensAll_of_killed <;> assumption)
