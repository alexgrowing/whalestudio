import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardBasisExtensionDetNeZero
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standard_basis_extension_det_ne_zero : ∀ {K : Type} [Field K] {J : Type} [Fintype J] {n : ℕ} (v : J → Fin n → K), LinearIndependent K v → ∃ e : J → Fin n, Function.Injective e ∧ (Matrix.of (Function.extend e v (fun i => Pi.single i (1 : K)))).det ≠ 0 := by
  first | exact @GlobalTheory.extend_linearIndependent_rows_by_standard_basis | exact GlobalTheory.extend_linearIndependent_rows_by_standard_basis | (intros; apply GlobalTheory.extend_linearIndependent_rows_by_standard_basis <;> assumption)
