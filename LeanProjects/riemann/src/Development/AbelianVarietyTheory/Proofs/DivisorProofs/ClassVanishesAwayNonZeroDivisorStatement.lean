import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonZeroDivisor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_vanishes_away_nonZeroDivisor : ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ (n i : ℤ) (z : Ht q (sp R) n i), pull _ (spMap (algebraMap R (FractionRing R))) _ _ z = 0 → ∃ g ∈ nonZeroDivisors R, pull _ (spMap (algebraMap R (Localization.Away g))) _ _ z = 0 := by
  first | (exact @GlobalTheory.EtC.classVanishesAwayNZD) | (exact GlobalTheory.EtC.classVanishesAwayNZD) | (intros; apply GlobalTheory.EtC.classVanishesAwayNZD  <;> assumption)
