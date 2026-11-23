import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PiTensorSubmoduleEqTopOfAbsolutelyIrreducibleSta
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurAndTensorSubmodule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarOfComm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensor_submodule_eq_top_of_absolutely_irreducible_stable : ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)), (∀ i, GlobalTheory.Chain.IoLift.AbsIrr (a i)) → ∀ N : Submodule ℂ (PiTensorProduct ℂ K), (∀ i g, ∀ x ∈ N, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one i (a i g) x ∈ N) → N ≠ ⊥ → N = ⊤ := by
  first | exact @GlobalTheory.TensorIrr.eq_top_of_stable | exact GlobalTheory.TensorIrr.eq_top_of_stable | (intros; apply GlobalTheory.TensorIrr.eq_top_of_stable <;> assumption)
