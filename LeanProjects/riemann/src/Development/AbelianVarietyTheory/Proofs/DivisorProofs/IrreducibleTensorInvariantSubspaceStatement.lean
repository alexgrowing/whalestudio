import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleTensorInvariantSubspace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_tensor_invariant_subspace : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V Z : Type) [AddCommGroup V] [Module ℂ V] (A : ι → Z → Module.End ℂ V) (H : ι → Submodule ℂ V), (∀ w, FiniteDimensional ℂ (H w)) → (∀ w, H w ≠ ⊥) → (∀ w z, ∀ v ∈ H w, A w z v ∈ H w) → (∀ w (N : Submodule ℂ V), N ≤ H w → (∀ z, ∀ v ∈ N, A w z v ∈ N) → N = ⊥ ∨ N = H w) → ∀ N : Submodule ℂ (⨂[ℂ] _ : ι, V), N ≤ GlobalTheory.KFixIrr.tensSpan H → (∀ w z, ∀ T ∈ N, GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w (A w z) T ∈ N) → N = ⊥ ∨ N = GlobalTheory.KFixIrr.tensSpan H := by
  first | exact @GlobalTheory.TensSpanIrr.tensSpan_irr | exact GlobalTheory.TensSpanIrr.tensSpan_irr | (intros; apply GlobalTheory.TensSpanIrr.tensSpan_irr <;> assumption)
