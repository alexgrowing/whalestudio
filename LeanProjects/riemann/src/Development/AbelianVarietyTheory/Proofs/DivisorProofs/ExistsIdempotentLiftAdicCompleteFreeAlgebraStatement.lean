import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftAdicCompleteFreeAlgebra
import Mathlib
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_lift_adicComplete_free_algebra : ∀ (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Free A Λ] [Module.Finite A Λ] (x : Λ), x * x - x ∈ I • (⊤ : Submodule A Λ) → ∃ e : Λ, IsIdempotentElem e ∧ e - x ∈ I • (⊤ : Submodule A Λ) := by
  first | (exact @GlobalTheory.IdemNewton.exists_idem) | (exact GlobalTheory.IdemNewton.exists_idem) | (intros; apply GlobalTheory.IdemNewton.exists_idem  <;> assumption)
