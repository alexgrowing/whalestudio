import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionDualNumberPointEqConstantCharZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_dualNumber_point_eq_constant_charZero : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (f : Sp (DualNumber K) ⟶ Sp K), f = spMap (algebraMap K (DualNumber K)) → (∀ x y : Over.mk f ⟶ A, x * y = y * x) → ∀ (u : Over.mk f ⟶ A) (n : ℕ), 0 < n → u ^ n = 1 → u.left = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left := by
  first | exact @GlobalTheory.TorsConst.torsion_eq_const | exact GlobalTheory.TorsConst.torsion_eq_const | (intros; apply GlobalTheory.TorsConst.torsion_eq_const <;> assumption)
