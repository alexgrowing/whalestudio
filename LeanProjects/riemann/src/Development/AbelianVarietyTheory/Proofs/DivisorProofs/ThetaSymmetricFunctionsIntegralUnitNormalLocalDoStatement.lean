import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsIntegralUnitNormalLocalDo
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSymmetricFunctions_integral_unit_normalLocalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (σ : SecAt t.G t.PP.L χ) (e : Fin N → FractionRing R), Odd m → 3 ≤ m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ) → NZ t.G t.PP.L χ σ → SymAt t.G t.PP.L t.PP.rig m (spMap (algebraMap R (FractionRing R)) ≫ χ) (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) e → ∃ e' : Fin N → R, (∀ j, algebraMap R (FractionRing R) (e' j) = e j) ∧ ∃ j, IsUnit (e' j) := by
  first | exact @GlobalTheory.UMin.IntTheta.integral_with_unit | exact GlobalTheory.UMin.IntTheta.integral_with_unit | (intros; apply GlobalTheory.UMin.IntTheta.integral_with_unit <;> assumption)
