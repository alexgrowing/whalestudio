import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

def transl {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : G ⟶ G :=
  𝟙 G * (Over.homMk G.hom (by simp) ≫ y)

def Near.chart {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]
    (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) : Option (Fin n) → (pullback N.U.hom π ⟶ G.left)
  | none => N.u
  | some k => N.u ≫ (transl (x k)⁻¹).left

@[simp] theorem Near.chart_none {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}
    [GrpObj G] (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) : N.chart x none = N.u := rfl

theorem Near.chart_some {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}
    [GrpObj G] (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) (k : Fin n) :
    N.chart x (some k) = N.u ≫ (transl (x k)⁻¹).left := rfl

end GlobalTheory.Mum
