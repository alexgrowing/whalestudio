import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicDivisibleDedekindFiniteTypeAlgClosed
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ c : CommRing.Pic B, ∃ d, d ^ q = c := by
  first | (exact @GlobalTheory.PicDiv.pic_divisible) | (exact GlobalTheory.PicDiv.pic_divisible) | (intros; apply GlobalTheory.PicDiv.pic_divisible  <;> assumption)
