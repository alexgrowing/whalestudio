import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def IsEtLevOver {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (l : D.La → (T ⟶ o.A)) : Prop :=
  (∀ x y, l (x + y) = l x * l y) ∧ (∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) ∧
    (∀ x ∈ wSub D w0 r, l x = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
      (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ l y = 1 → y ∈ wSub D w0 r) ∧
      ∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
        ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ l y = g

def ptOf {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {T : Scheme.{0}} {t : T ⟶ S} {s₁ : T ⟶ Sp R} {o : Obj b N s}
    {o₁ : Obj b N s₁} (m : ObjMap o₁ o t) (l : 𝟙_ (Over T) ⟶ o₁.A) : Over.mk t ⟶ o.A :=
  Over.homMk (l.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w l]
    exact Category.id_comp t)

def levAct {w0 : Ideal (𝓞 D.F)} {r : ℕ} (g : LevGrp D w0 r) (y : D.La) : D.La :=
  Function.surjInv (Submodule.mkQ_surjective (wSub D w0 r)) (g ((wSub D w0 r).mkQ y))

theorem mkQ_levAct {w0 : Ideal (𝓞 D.F)} {r : ℕ} (g : LevGrp D w0 r) (y : D.La) :
    (wSub D w0 r).mkQ (levAct g y) = g ((wSub D w0 r).mkQ y) :=
  Function.surjInv_eq _ _

end GlobalTheory.UPel.HT.EtLev
