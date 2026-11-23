import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem unitRes_top_injective {S : Scheme.{0}} {T : Over S} :
    Function.Injective (Out.unitRes (T := T) ⊤) := by
  intro a b h
  have hi : IsIso (⊤ : T.left.Opens).ι := inferInstanceAs (IsIso T.left.topIso.hom)
  have hi' : IsIso (⊤ : T.left.Opens).ι.appTop := inferInstanceAs (IsIso ((⊤ : T.left.Opens).ι.app ⊤))
  have hb : Function.Injective (⊤ : T.left.Opens).ι.appTop.hom :=
    (ConcreteCategory.bijective_of_isIso (⊤ : T.left.Opens).ι.appTop).1
  exact Units.ext (hb (congrArg Units.val h))

theorem unitOn_injective_of_commRing {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  have hb : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
  exact Units.ext (hb (congrArg Units.val h))

theorem weilIs_unique_fieldPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (n : ℤ) (x y : Over.mk t ⟶ G) (c c' : kˣ), Out.WeilIs G L n x y (unitOn c) → Out.WeilIs G L n x y (unitOn c') → c = c' := by
  intro S G _ L hL k _ t n x y c c' h h'
  let p : (Over.mk t).left := (⊥ : PrimeSpectrum k)
  have top : ∀ V : (Over.mk t).left.Opens, p ∈ V → V = ⊤ := fun V hV =>
    eq_top_iff.2 fun q _ => by
      have : q = p := Subsingleton.elim (α := PrimeSpectrum k) q p
      exact this ▸ hV
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := h p
  obtain ⟨V', hV', -, H'⟩ := h' p
  obtain rfl := top V hV
  obtain rfl := top V' hV'
  exact unitOn_injective_of_commRing (unitRes_top_injective
    (H1.commIsOf_unique hL θx θy _ _ (H θx θy hx hy) (H' θx θy hx hy)))

end GlobalTheory
