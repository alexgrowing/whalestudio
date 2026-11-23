import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixSandwichTraceEq
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_sandwich_trace_eq : ∀ (A : Type) [CommRing A] [IsDomain A] (h : ℕ) (μ : A) (F G X Y : Matrix (Fin h) (Fin h) A), μ ≠ 0 → G * F = μ • (1 : Matrix (Fin h) (Fin h) A) → F * X = Y * F → F * G = μ • (1 : Matrix (Fin h) (Fin h) A) ∧ X * G = G * Y ∧ Y.trace = X.trace := by
  first | exact @GlobalTheory.trace_eq_of_intertwined_by_quasi_inverse | exact GlobalTheory.trace_eq_of_intertwined_by_quasi_inverse | (intros; apply GlobalTheory.trace_eq_of_intertwined_by_quasi_inverse <;> assumption)
