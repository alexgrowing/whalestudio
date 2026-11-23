import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFrobeniusTwistBijectiveRelFrobenius
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius : ∀ (p : ℕ) [Fact p.Prime] (B : Base p fun _ _ _ => True) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), Function.Bijective (B.smap trivial trivial (frobProj (p_eq_zero p k) G)) ∧ (∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G) (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m) ∧ ∀ m n, B.smap trivial trivial (frobProj (p_eq_zero p k) G) n = B.map trivial trivial (verschiebung (p_eq_zero p k) G) m → B.F G trivial n = p • m := by
  first | exact @GlobalTheory.Dieu.frobTwist_module | exact GlobalTheory.Dieu.frobTwist_module | (intros; apply GlobalTheory.Dieu.frobTwist_module <;> assumption)
