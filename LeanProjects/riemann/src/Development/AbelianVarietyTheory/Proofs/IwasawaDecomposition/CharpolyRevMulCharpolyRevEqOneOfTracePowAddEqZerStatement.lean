import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevMulCharpolyRevEqOneOfTracePowAddEqZer
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpolyRev_mul_eq_one_of_trace_pow_add_eq_zero : ∀ {K R : Type} [Field K] [CharZero K] [CommRing R] [Algebra K R] {p q : ℕ} (M : Matrix (Fin p) (Fin p) R) (N : Matrix (Fin q) (Fin q) R), (∀ k, 1 ≤ k → (M ^ k).trace + (N ^ k).trace = 0) → M.charpolyRev * N.charpolyRev = 1 := by
  first | exact @GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero | exact GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero | (intros; apply GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero <;> assumption)
