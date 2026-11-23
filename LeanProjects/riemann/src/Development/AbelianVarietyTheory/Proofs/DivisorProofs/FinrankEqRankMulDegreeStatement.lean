import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqRankMulDegree
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eq_rank_mul_degree : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (r : ℕ) (x : Fin r → M), LinearIndependent (𝓞 F) x → ∀ c : 𝓞 F, c ≠ 0 → (∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x)) → Module.finrank ℤ M = r * Module.finrank ℚ F := by
  first | exact @GlobalTheory.finrank_int_eq_of_span_smul | exact GlobalTheory.finrank_int_eq_of_span_smul | (intros; apply GlobalTheory.finrank_int_eq_of_span_smul <;> assumption)
