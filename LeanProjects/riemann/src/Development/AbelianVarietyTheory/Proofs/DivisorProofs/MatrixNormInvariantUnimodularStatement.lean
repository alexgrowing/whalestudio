import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixNormInvariantUnimodular
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open GlobalTheory.TriFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_norm_invariant_unimodular : ∀ {C : Type} [NormedField C] [IsUltrametricDist C] {r : ℕ} (Q Q' N : Matrix (Fin r) (Fin r) C), Q' * Q = 1 → (∀ l k, ‖Q l k‖ ≤ 1) → (∀ l k, ‖Q' l k‖ ≤ 1) → ∀ i, matNorm (Q * N) i = matNorm N i := by
  first | exact @GlobalTheory.TriFrame.gl_invariant | exact GlobalTheory.TriFrame.gl_invariant | (intros; apply GlobalTheory.TriFrame.gl_invariant <;> assumption)
