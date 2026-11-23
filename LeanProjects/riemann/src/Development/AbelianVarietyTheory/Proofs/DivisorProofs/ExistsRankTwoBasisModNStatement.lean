import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankTwoBasisModN
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_two_basis_mod_N : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M], Module.finrank ℤ M = 2 * Module.finrank ℚ F → ∀ N : ℕ, 1 ≤ N → ∃ x : Fin 2 → M, (∀ m : M, ∃ (a b : 𝓞 F) (m' : M), m = a • x 0 + b • x 1 + N • m') ∧ ∀ a b : 𝓞 F, (∃ m' : M, a • x 0 + b • x 1 = N • m') → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  first | exact @GlobalTheory.LatticeModN.exists_gen_modN | exact GlobalTheory.LatticeModN.exists_gen_modN | (intros; apply GlobalTheory.LatticeModN.exists_gen_modN <;> assumption)
