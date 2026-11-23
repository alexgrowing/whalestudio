import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSemilinearMatrixIterateEqZeroOfNilpoten
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusSemilinearMatrix_iterate_eq_zero_of_nilpotent : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := by
  first | exact @GlobalTheory.frobSemilinear_iterate_eq_zero | exact GlobalTheory.frobSemilinear_iterate_eq_zero | (intros; apply GlobalTheory.frobSemilinear_iterate_eq_zero <;> assumption)
