import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockTriVecMulEqSinglePred
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockTri_vecMul_eq_single_pred : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ), Monotone b → ∀ (k k' : Fin r), k'.val + 1 = k.val → ∀ l : Fin r → F, l ≠ 0 → (∀ i, l i ≠ 0 → i < k ∧ b i = b k) → ∃ h : blockTri (κ := F) b, (∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k) ∧ Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Pi.single k' 1 := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_blockTri_vecMul_eq_single | exact GlobalTheory.FinGL.LeviWh.exists_blockTri_vecMul_eq_single | (intros; apply GlobalTheory.FinGL.LeviWh.exists_blockTri_vecMul_eq_single <;> assumption)
