import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureOfForallDualVanish
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_of_forall_clm_vanish : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by
  first | exact @GlobalTheory.mem_closure_of_forall_dual_vanish | exact GlobalTheory.mem_closure_of_forall_dual_vanish | (intros; apply GlobalTheory.mem_closure_of_forall_dual_vanish <;> assumption)
