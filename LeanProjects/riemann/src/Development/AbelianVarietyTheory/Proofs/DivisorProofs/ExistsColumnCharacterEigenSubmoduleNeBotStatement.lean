import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_columnCharacter_eigenSubmodule_ne_bot : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), Monotone b → (∀ p : blockTri (κ := F) b, (∀ i j, b i = b j → ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) → σ p = 1) → ∀ k : Fin r, eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ → ∃ l : Fin r → F, (∀ i, l i ≠ 0 → i < k ∧ b i = b k) ∧ eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | exact GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | (intros; apply GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot <;> assumption)
