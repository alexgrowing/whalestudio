import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalVanishingCohomology
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_local_vanishing_cohomology : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (m i : ℤ), 1 ≤ m → ∀ y : Ht q (sp B) m i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A') (_ : Algebra.Etale B A'), IsNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ y = 0 := by
  first | (exact @GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero) | (exact GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero) | (intros; apply GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero <;> assumption)
