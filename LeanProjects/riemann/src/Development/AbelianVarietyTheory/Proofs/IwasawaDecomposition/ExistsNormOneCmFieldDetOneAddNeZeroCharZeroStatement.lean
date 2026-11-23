import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormOneCmFieldDetOneAddNeZeroCharZero
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normOne_cmField_det_one_add_ne_zero_charZero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (K : Type) [Field K] [CharZero K] (n : ℕ) (M : (L →+* K) → Matrix (Fin n) (Fin n) K), ∃ u : L, u * (IsCMField.complexConj L : L →+* L) u = 1 ∧ ∀ σ : L →+* K, (1 + σ u • M σ).det ≠ 0 := by
  first | exact @GlobalTheory.CMScalar.exists_unit_norm_one_det_ne_zero | exact GlobalTheory.CMScalar.exists_unit_norm_one_det_ne_zero | (intros; apply GlobalTheory.CMScalar.exists_unit_norm_one_det_ne_zero <;> assumption)
