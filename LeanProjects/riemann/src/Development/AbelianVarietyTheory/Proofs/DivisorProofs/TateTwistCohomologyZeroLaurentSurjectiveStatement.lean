import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroLaurentSurjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_zero_laurent_surjective : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T], IsUnit (q : T) → ∀ (i : ℤ) (y : Ht q (sp (LaurentPolynomial T)) 0 i), ∃ z : Ht q (sp T) 0 i, pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) _ 0 z = y := by
  first | (exact @GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq) | (exact GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq) | (intros; apply GlobalTheory.EtC.MultiplicativeGroupGlobalSections.exists_ht_zero_pull_laurent_eq  <;> assumption)
