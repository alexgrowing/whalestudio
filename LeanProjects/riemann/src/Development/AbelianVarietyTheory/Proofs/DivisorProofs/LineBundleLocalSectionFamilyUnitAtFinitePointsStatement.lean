import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLocalSectionFamilyUnitAtFinitePoints
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionFamilyZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleLocalSectionFamily_unit_at_finite_points : ∀ (X : Scheme.{0}) (L : LB X) (W : X.Opens) (J : Type) (D : J → X.Opens), (∀ j, D j ≤ W) → ∀ (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (F : Set X), F.Finite → ∀ (a : X → Γ(X, W)), (∀ x ∈ F, x ∈ X.basicOpen (a x)) → (∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ∉ X.basicOpen (a x)) → ∀ (E : X → ∀ j, Γ(X, D j)), (∀ x ∈ F, GlobalTheory.Pinch.IsSecFam L D k hD (E x)) → (∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (E x j))) → ∃ e : ∀ j, Γ(X, D j), GlobalTheory.Pinch.IsSecFam L D k hD e ∧ ∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) := by
  first | exact @GlobalTheory.Pinch.secFam_unit_at_finite | exact GlobalTheory.Pinch.secFam_unit_at_finite | (intros; apply GlobalTheory.Pinch.secFam_unit_at_finite <;> assumption)
