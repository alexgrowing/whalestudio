import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KerReductionLeRangeReductionOfMulEqSmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_reduction_le_range_reduction_of_mul_eq_smul : ∀ {O : Type} [CommRing O] [IsDomain O] {k : Type} [Field k] (r : O →+* k), Function.Surjective r → ∀ {n : ℕ} (M N : Matrix (Fin n) (Fin n) O) (π : O), π ≠ 0 → (∀ t : O, r t = 0 → ∃ s, t = π * s) → M * N = π • (1 : Matrix (Fin n) (Fin n) O) → ∀ (v : Fin n → k), N.map r *ᵥ v = 0 → ∃ u, v = M.map r *ᵥ u := by
  first | exact @GlobalTheory.ker_map_subset_range_map_of_mul_eq_smul | exact GlobalTheory.ker_map_subset_range_map_of_mul_eq_smul | (intros; apply GlobalTheory.ker_map_subset_range_map_of_mul_eq_smul <;> assumption)
