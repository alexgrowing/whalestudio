import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem grpPullback_mul_section {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G']
    {f : B' ⟶ B} {φ : G'.left ⟶ G.left} (H : IsGrpPullback G' G f φ) (x y : baseOver B' ⟶ G')
    (h h' : baseOver B ⟶ G) (hx : x.left ≫ φ = f ≫ h.left) (hy : y.left ≫ φ = f ≫ h'.left) :
    (x * y).left ≫ φ = f ≫ (h * h').left := by
  let U : Over.mk ((baseOver B').hom ≫ f) ⟶ baseOver B := Over.homMk f (by simp)
  have e := H.2 (baseOver B') x y (U ≫ h) (U ≫ h') hx.symm hy.symm
  rw [← MonObj.comp_mul] at e
  exact e.symm

theorem extends_mul (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ)
    [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a b : S.Gam) (h h' : baseOver (Sp u.V) ⟶ u.G)
    (ha : Extends u a h) (hb : Extends u b h') : Extends u (a + b) (h * h') := by
  obtain ⟨x, x1, x2, x3⟩ := ha
  obtain ⟨y, y1, y2, y3⟩ := hb
  have := u.U.gen_hom
  let X : baseOver (Sp (FractionRing u.V)) ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk x x2
  let Y : baseOver (Sp (FractionRing u.V)) ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk y y2
  refine ⟨(X * Y).left, ?_, Over.w (X * Y), ?_⟩
  · exact grpPullback_mul_section (isGrpPullback_pullback u.G (jK u.V)) X Y h h' x1 y1
  · rw [ρ.pt_add]
    exact grpPullback_mul_section
      (((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl) X Y _ _ x3 y3

end GlobalTheory.UnitTheta
