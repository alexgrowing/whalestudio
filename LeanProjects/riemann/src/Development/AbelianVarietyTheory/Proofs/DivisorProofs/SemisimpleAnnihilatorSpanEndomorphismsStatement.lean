import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemisimpleAnnihilatorSpanEndomorphisms
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_annihilator_span_endomorphisms : ∀ (R : Type) [Ring R] (M : Type) [AddCommGroup M] [Module R M], IsSemisimpleModule R M → ∀ (n : ℕ) (w : Fin n → M) (v : M), (∀ a : R, (∀ j, a • w j = 0) → a • v = 0) → ∃ f : Fin n → (M →ₗ[R] M), v = ∑ j, f j (w j) := by
  first | exact @GlobalTheory.semisimple_mem_sum_endo_images | exact GlobalTheory.semisimple_mem_sum_endo_images | (intros; apply GlobalTheory.semisimple_mem_sum_endo_images <;> assumption)
