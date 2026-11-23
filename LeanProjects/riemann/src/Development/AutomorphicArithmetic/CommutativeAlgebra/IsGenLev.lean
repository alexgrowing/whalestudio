import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel

noncomputable section

namespace UpperTheory.D3

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {V E κ : Type} [CommRing V] [Field E] [Field κ] [Algebra V E] {s : Sp V ⟶ Sp R}

def RedOne (ρ : V →+* κ) (o : Obj b N s) (g : Over.mk (spMap (algebraMap V E)) ⟶ o.A) : Prop :=
  ∃ g' : 𝟙_ (Over (Sp V)) ⟶ o.A, spMap (algebraMap V E) ≫ g'.left = g.left ∧
    spMap ρ ≫ g'.left = spMap ρ ≫ (1 : 𝟙_ (Over (Sp V)) ⟶ o.A).left

def IsGenLev (o : Obj b N s) (w : Ideal (𝓞 D.F)) (ℓ : D.La → (Over.mk (spMap (algebraMap V E)) ⟶ o.A)) : Prop :=
  (∀ x y, ℓ (x + y) = ℓ x * ℓ y) ∧ (∀ (c : D.O) x, ℓ (c • x) = ℓ x ≫ o.act.act c) ∧
    (∀ y, ℓ y = 1 ↔ y ∈ wSub D w 1) ∧
    ∀ g : Over.mk (spMap (algebraMap V E)) ⟶ o.A, KilledBy o w g → ∃ y, ℓ y = g

end UpperTheory.D3
