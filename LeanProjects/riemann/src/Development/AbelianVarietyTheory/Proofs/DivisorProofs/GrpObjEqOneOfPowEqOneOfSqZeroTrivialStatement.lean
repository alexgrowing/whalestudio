import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjEqOneOfPowEqOneOfSqZeroTrivial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpObj_eq_one_of_pow_eq_one_of_sqZero_trivial : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (G : Over (Sp C)) [GrpObj G] (n : ℕ), IsUnit (n : C) → ∀ (T : Over (Sp C)) (z : T ⟶ G), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ z = 1) → z ^ n = 1 → z = 1 := by
  first | (exact @GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick) | (exact GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick) | (intros; apply GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick  <;> assumption)
