import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicTraitLiftFiniteThroughPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicTrait_lift_finite_through_point : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ (p : ℕ) [Fact p.Prime] (Y : Sp (OO p) ⟶ Z) (w : X), f w = (gPt p ≫ Y) (IsLocalRing.closedPoint (PadicAlgCl p)) → ∃ y : Sp (OO p) ⟶ X, y ≫ f = Y ∧ (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) = w := by
  first | exact @GlobalTheory.UPoinc.exists_lift_finite_through_point | exact GlobalTheory.UPoinc.exists_lift_finite_through_point | (intros; apply GlobalTheory.UPoinc.exists_lift_finite_through_point <;> assumption)
