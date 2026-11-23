import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSurjModIdealExistsCongrOneMulMemRange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sub_one_mem_mul_mem_range_of_finite_surj_mod : ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C), f.Finite → ∀ J : Ideal B, Function.Surjective ((Ideal.Quotient.mk (J.map f)).comp f) → ∃ r : B, r - 1 ∈ J ∧ ∀ c : C, ∃ b : B, f r * c = f b := by
  first | exact @GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range | exact GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range | (intros; apply GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range <;> assumption)
