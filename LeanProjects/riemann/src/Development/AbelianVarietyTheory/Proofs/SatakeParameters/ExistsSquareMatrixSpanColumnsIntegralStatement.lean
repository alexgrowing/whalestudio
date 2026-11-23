import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSquareMatrixSpanColumnsIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_matrix_span_columns_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin n) ι L), ∃ b : Matrix (Fin n) (Fin n) L, ∀ v : Fin n → L,
      (∃ u : ι → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = M *ᵥ u) ↔ ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = b *ᵥ t := by
  first | exact @GlobalTheory.Hk3.HoweG.exists_square_span_cols | exact GlobalTheory.Hk3.HoweG.exists_square_span_cols | (intros; apply GlobalTheory.Hk3.HoweG.exists_square_span_cols <;> assumption)
