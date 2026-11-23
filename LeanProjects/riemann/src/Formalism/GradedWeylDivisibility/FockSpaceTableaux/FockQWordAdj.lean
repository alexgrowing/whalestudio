import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

lemma leadj_applyWord_cons {r n : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) ℚ) :
    applyWord ℚ (x :: w) F = rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w F) := by
  rfl

lemma leadj_applyWord_append {r n : ℕ} (l1 l2 : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) ℚ) :
    applyWord ℚ (l1 ++ l2) F = applyWord ℚ l1 (applyWord ℚ l2 F) := by
  unfold applyWord
  rw [List.foldr_append]

lemma leadj_transposeWord_cons {r : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (x :: w) = transposeWord w ++ [(x.2.1, x.1, x.2.2)] := by
  simp [transposeWord]

theorem fock_space_word_adjoint : FockQWordAdj := by
  intro r n w
  induction w with
  | nil => intro F G; simp [applyWord, transposeWord]
  | cons x w ih =>
    intro F G
    rw [leadj_applyWord_cons, fockQRowDivAdj, ih, leadj_transposeWord_cons, leadj_applyWord_append]
    simp [applyWord]

end Formalism.GradedWeylDivisibility
