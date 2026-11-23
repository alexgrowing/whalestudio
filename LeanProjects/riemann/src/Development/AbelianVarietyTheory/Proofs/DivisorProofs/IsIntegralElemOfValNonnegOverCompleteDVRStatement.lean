import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemOfValNonnegOverCompleteDVR
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralElem_of_val_nonneg_over_completeDVR : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v → ∀ z : F, 0 ≤ v z → ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).IsIntegralElem z := by
  first | exact @GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg | exact GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg | (intros; apply GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg <;> assumption)
