import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMul
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poly_entries_conj_left_right_mul : ∀ (n : ℕ) (a b : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, Q.totalDegree ≤ P.totalDegree ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (a * g * b) z.1 z.2) (fun z : Fin n × Fin n => star ((a * g * b) z.1 z.2))) P = MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (g) z.1 z.2) (fun z : Fin n × Fin n => star ((g) z.1 z.2))) Q := by
  first | exact @GlobalTheory.PolyEntryMul.main | exact GlobalTheory.PolyEntryMul.main | (intros; apply GlobalTheory.PolyEntryMul.main <;> assumption)
