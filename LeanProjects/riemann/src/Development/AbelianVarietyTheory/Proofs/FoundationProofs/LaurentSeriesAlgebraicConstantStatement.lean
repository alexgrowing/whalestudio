import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesAlgebraicConstant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_series_algebraic_constant : ∀ (k : Type) [Field k] (f : LaurentSeries k), (∃ P : k[X], P ≠ 0 ∧ eval₂ HahnSeries.C f P = 0) → ∃ c : k, f = HahnSeries.C c := by
  first | exact @GlobalTheory.laurentSeries_eq_C_of_root | exact GlobalTheory.laurentSeries_eq_C_of_root | (intros; apply GlobalTheory.laurentSeries_eq_C_of_root <;> assumption)
