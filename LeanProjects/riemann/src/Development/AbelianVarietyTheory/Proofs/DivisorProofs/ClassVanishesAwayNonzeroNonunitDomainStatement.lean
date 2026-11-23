import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonzeroNonunitDomain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain : ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B], ¬ IsField B → IsUnit (q : B) → ∀ (n i : ℤ) (x : Ht q (sp B) n i), pull _ (spMap (algebraMap B (FractionRing B))) _ _ x = 0 → ∃ f : B, f ≠ 0 ∧ ¬ IsUnit f ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.classVanishesAway) | (exact GlobalTheory.EtC.classVanishesAway) | (intros; apply GlobalTheory.EtC.classVanishesAway  <;> assumption)
