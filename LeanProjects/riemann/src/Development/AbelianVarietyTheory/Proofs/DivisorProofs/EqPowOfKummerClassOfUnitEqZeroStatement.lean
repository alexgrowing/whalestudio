import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfKummerClassOfUnitEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → ∀ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = 0 → ∃ v, u = v ^ q := by
  first | (exact @GlobalTheory.EtC.eq_pow_of_kum_eq_zero) | (exact GlobalTheory.EtC.eq_pow_of_kum_eq_zero) | (intros; apply GlobalTheory.EtC.eq_pow_of_kum_eq_zero  <;> assumption)
