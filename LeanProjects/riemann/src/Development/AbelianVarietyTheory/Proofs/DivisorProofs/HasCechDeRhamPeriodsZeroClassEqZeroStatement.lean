import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsZeroClassEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCechDeRhamPeriods_zero_class_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ q, IsPer u.ex u.Λ 0 q → q = 0 := by
  first | exact @GlobalTheory.CechPer.zero_periods_eq_zero | exact GlobalTheory.CechPer.zero_periods_eq_zero | (intros; apply GlobalTheory.CechPer.zero_periods_eq_zero <;> assumption)
