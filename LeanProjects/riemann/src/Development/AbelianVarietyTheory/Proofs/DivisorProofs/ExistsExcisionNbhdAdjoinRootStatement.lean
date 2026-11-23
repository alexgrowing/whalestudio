import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExcisionNbhdAdjoinRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit : ∀ (A : Type) [CommRing A] (h : A) (q : ℕ), IsUnit (q : A) → ∀ ε r : A, IsUnit ε → ε - r ^ q ∈ Ideal.span {h} → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), IsExcisionNbhd A A' h ∧ ∃ x : A', algebraMap A A' ε = x ^ q := by
  first | (exact @GlobalTheory.EtC.exists_excisionNbhd_adjoin_root) | (exact GlobalTheory.EtC.exists_excisionNbhd_adjoin_root) | (intros; apply GlobalTheory.EtC.exists_excisionNbhd_adjoin_root  <;> assumption)
