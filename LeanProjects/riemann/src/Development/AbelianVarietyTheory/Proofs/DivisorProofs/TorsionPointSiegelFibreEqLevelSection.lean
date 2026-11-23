import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem torsion_isLev : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (y : S ⟶ X) (α : A.left ⟶ c.A.left), IsGrpPullback A c.A y α → ∀ (F : Type) [Field F] [IsAlgClosed F] (t : Sp F ⟶ S) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ l, x.left ≫ α = t ≫ y ≫ (c.lev l).left := by
  intro X g n B _ ζ sX c hζ S A _ y α hα F _ _ t x hx
  let β : B →+* F := (Spec.preimage ((t ≫ y) ≫ sX)).hom
  obtain ⟨-, hs, -⟩ := c.geom F (t ≫ y) β (hζ.map β).unit (Spec.map_preimage _).symm rfl
  have hx₁ : pushHom hα (Over.mk t) x ^ n = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨a, ha⟩ := hs _ hx₁
  have hu : (toUnit (Over.mk (t ≫ y))).left = t ≫ y := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (t ≫ y) ≫ (c.lev a).left = x.left ≫ α := by
    rw [← hu]
    exact congrArg (fun q => q.left) ha
  exact ⟨a, by rw [← e, Category.assoc]⟩

end GlobalTheory.TInj
