import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassGroupDedekindAlgClosedDivisible
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classGroup_dedekind_algClosed_divisible : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), (q : k) ≠ 0 → ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := by
  first | (exact @GlobalTheory.PicDiv.classGroup_divisible) | (exact GlobalTheory.PicDiv.classGroup_divisible) | (intros; apply GlobalTheory.PicDiv.classGroup_divisible <;> assumption)
