import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularBlockForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open GlobalTheory.TriFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_block_form : ∀ {R : Type} [CommRing R] {r : ℕ} (P' : GL (Fin r) R), ∃ P : GL (Fin (r+1)) R, (P : Matrix (Fin (r+1)) (Fin (r+1)) R) 0 0 = 1 ∧ (∀ k : Fin r, (P : Matrix (Fin (r+1)) (Fin (r+1)) R) 0 k.succ = 0) ∧ (∀ l : Fin r, (P : Matrix (Fin (r+1)) (Fin (r+1)) R) l.succ 0 = 0) ∧ ∀ l k : Fin r, (P : Matrix (Fin (r+1)) (Fin (r+1)) R) l.succ k.succ = (P' : Matrix (Fin r) (Fin r) R) l k := by
  first | exact @GlobalTheory.CornerExtend.exists_gl_corner_extend | exact GlobalTheory.CornerExtend.exists_gl_corner_extend | (intros; apply GlobalTheory.CornerExtend.exists_gl_corner_extend <;> assumption)
