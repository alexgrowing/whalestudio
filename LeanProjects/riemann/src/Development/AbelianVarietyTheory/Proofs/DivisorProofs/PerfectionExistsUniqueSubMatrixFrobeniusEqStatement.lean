import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectionExistsUniqueSubMatrixFrobeniusEq
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfection_existsUnique_sub_matrix_frobenius_eq : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] (Q : Matrix ι ι (Perfection S p)), (∀ n : ℕ, ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k))^[K] z = 0) → ∀ c : ι → Perfection S p, ∃! x : ι → Perfection S p, x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k)) = c := by
  first | exact @GlobalTheory.perfection_frobenius_solve | exact GlobalTheory.perfection_frobenius_solve | (intros; apply GlobalTheory.perfection_frobenius_solve <;> assumption)
