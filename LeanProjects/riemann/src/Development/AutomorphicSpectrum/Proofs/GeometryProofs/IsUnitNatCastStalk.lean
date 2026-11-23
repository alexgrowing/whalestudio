import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem isUnit_natCast_stalk (X : Scheme.{0}) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ X) (n : ℕ) (hn : n ≠ 0) :
    IsUnit ((n : X.presheaf.stalk (centre z))) := by
  set x := IsLocalRing.closedPoint L
  have hL : IsUnit (n : L) := (Nat.cast_ne_zero.mpr hn).isUnit
  let φ : L →+* (Sp L).presheaf.stalk x :=
    ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (Sp L).presheaf.germ ⊤ x trivial).hom
  have h2 : IsUnit (n : (Sp L).presheaf.stalk x) := by
    simpa using hL.map φ
  have h3 : IsUnit ((z.stalkMap x).hom (n : X.presheaf.stalk (z x))) := by
    simpa using h2
  haveI : IsLocalHom (z.stalkMap x).hom := z.prop x
  exact (isUnit_map_iff (z.stalkMap x).hom _).mp h3

end GlobalTheory.CompanionTheory.Ar.FlagFib
