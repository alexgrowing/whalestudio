import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

def Extends (u : ρ.UTest p y₀) (a : S.Gam) (h : baseOver (Sp u.V) ⟶ u.G) : Prop :=
  ∃ x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V), x ≫ pullback.fst _ _ = jK u.V ≫ h.left ∧
    x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left

theorem integral_iff (u : ρ.UTest p y₀) (a : S.Gam) : u.Integral a ↔ ∃ h, Extends u a h :=
  ⟨fun ⟨h, x, e, H⟩ => ⟨Over.homMk h e, x, H⟩, fun ⟨h, x, H⟩ => ⟨h.left, x, Over.w h, H⟩⟩

end GlobalTheory.UnitTheta
