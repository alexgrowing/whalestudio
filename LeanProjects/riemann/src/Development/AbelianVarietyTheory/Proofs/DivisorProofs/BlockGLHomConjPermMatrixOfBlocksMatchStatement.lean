import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockGLHomConjPermMatrixOfBlocksMatch
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockGLHom_conj_permMatrix_of_blocks_match : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ) (w : Equiv.Perm (Fin r)), (∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j)) → ∀ i : Fin r, (block b (b i)).card = (block b' (b' (w i))).card ∧ ∀ (d : ℕ) (h : (block b (b i)).card = d) (h' : (block b' (b' (w i))).card = d), ∃ π : GL (Fin d) F, ∀ g : GL (Fin d) F, (blockHom F b' (b' (w i)) h' (π * g * π⁻¹) : GL (Fin r) F) * permGL F w = permGL F w * (blockHom F b (b i) h g : GL (Fin r) F) := by
  first | exact @GlobalTheory.Proof.BlockConj.blockHom_conj_permGL | exact GlobalTheory.Proof.BlockConj.blockHom_conj_permGL | (intros; apply GlobalTheory.Proof.BlockConj.blockHom_conj_permGL <;> assumption)
