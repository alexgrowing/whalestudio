import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnBlocksSpanFlag_of_block_triangular : ∀ (n a : ℕ) (j : Fin a → ℕ) (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ k i, i < k → p k i = 0 ∧ q k i = 0) → (∀ i, A i = ∑ k, B k * p k i) → (∀ i, B i = ∑ k, A k * q k i) → SpansFlag A W → SpansFlag B W := by
  first | exact @GlobalTheory.LeviIso.spansFlag_of_triangular | exact GlobalTheory.LeviIso.spansFlag_of_triangular | (intros; apply GlobalTheory.LeviIso.spansFlag_of_triangular <;> assumption)
