import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldOfUniquePrimeStalk
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_of_unique_prime_stalk : ∀ (R : CommRingCat.{0}) (q : Spec R), (∀ q' : Spec R, q' = q) → IsField ((Spec R).presheaf.stalk q) → IsField R := by
  first | exact @GlobalTheory.isField_of_spec_singleton_stalk_isField | exact GlobalTheory.isField_of_spec_singleton_stalk_isField | (intros; apply GlobalTheory.isField_of_spec_singleton_stalk_isField <;> assumption)
