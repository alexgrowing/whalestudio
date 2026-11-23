import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnitsLiftAlongThickening
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_units_lift_along_thickening : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (T₂ T₀ : Over S) (k : T₀ ⟶ T₂), IsAffine T₂.left → IsClosedImmersion k.left → Surjective k.left → Function.Surjective (Units.map (A ◁ k).left.appTop.hom.toMonoidHom) := by
  first | exact @GlobalTheory.DualOpen.units_lift_of_thickening | exact GlobalTheory.DualOpen.units_lift_of_thickening | (intros; apply GlobalTheory.DualOpen.units_lift_of_thickening <;> assumption)
