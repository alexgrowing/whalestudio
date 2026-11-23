import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetsInAffineOpenAbelianSchemeRelAmple
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteSetsInAffineOpen_abelianScheme_relAmple : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → FinAff A.left := by
  first | exact @GlobalTheory.DualCon.FinAffNoeth.finAff_of_relAmple_noetherian | exact GlobalTheory.DualCon.FinAffNoeth.finAff_of_relAmple_noetherian | (intros; apply GlobalTheory.DualCon.FinAffNoeth.finAff_of_relAmple_noetherian <;> assumption)
