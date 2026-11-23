import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedIntegralBasis
import Mathlib
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_matrix_adapted_to_flag : ∀ (F : Type) [Field F] (n R : ℕ) (W : Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)), Monotone W → ∃ g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ, ∀ (k : Fin (R + 1)) (j : Fin n), (j : ℕ) < Module.finrank (LaurentSeries F) (W k) → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W k := by
  first | exact @GlobalTheory.LaurentFlagBasis.adapted_integral_basis | exact GlobalTheory.LaurentFlagBasis.adapted_integral_basis | (intros; apply GlobalTheory.LaurentFlagBasis.adapted_integral_basis <;> assumption)
