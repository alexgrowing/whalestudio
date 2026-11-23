import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqOneOfForallPrimeMaximal
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_eq_one_of_forall_prime_maximal : ∀ (R : Type) [CommRing R], (∀ P : Ideal R, P.IsPrime → P.IsMaximal) → ∀ c : CommRing.Pic R, c = 1 := by
  first | (exact @GlobalTheory.pic_eq_one_of_forall_isMaximal) | (exact GlobalTheory.pic_eq_one_of_forall_isMaximal) | (intros; apply GlobalTheory.pic_eq_one_of_forall_isMaximal  <;> assumption)
