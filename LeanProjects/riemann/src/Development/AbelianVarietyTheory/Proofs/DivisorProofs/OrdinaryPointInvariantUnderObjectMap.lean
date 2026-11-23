import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Torsor
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace ObjMapPts

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S₂ : Scheme.{0}} {s₁ : S ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o : Obj b N s₁} {o₂ : Obj b N s₂} {f : S ⟶ S₂}

def push (m : ObjMap o o₂ f) {k : Type} [CommRing k] (x : Sp k ⟶ S) (g : Over.mk x ⟶ o.A) : Over.mk (x ≫ f) ⟶ o₂.A :=
  Over.homMk (g.left ≫ m.φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [m.cart.1.w, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w g))

@[simp] theorem push_left (m : ObjMap o o₂ f) {k : Type} [CommRing k] (x : Sp k ⟶ S) (g : Over.mk x ⟶ o.A) :
    (push m x g).left = g.left ≫ m.φ := rfl

end ObjMapPts

end GlobalTheory.UPel.HT.ES
