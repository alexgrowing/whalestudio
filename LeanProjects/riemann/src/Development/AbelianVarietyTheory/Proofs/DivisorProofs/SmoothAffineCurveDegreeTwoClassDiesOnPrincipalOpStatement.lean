import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDegreeTwoClassDiesOnPrincipalOp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localization_away_pull_eq_zero_Ht_two : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ (i : ℤ) (x : Ht q (sp B) 2 i), ∃ f : B, f ≠ 0 ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (exact GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (intros; apply GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen <;> assumption)
