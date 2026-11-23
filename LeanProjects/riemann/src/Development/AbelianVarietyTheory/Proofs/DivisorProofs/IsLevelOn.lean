import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegRel
import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

def IsLevelOn {Y : Scheme.{0}} {s : Y ⟶ Sp R} (o₀ : Pre b s) {G : Over Y} [GrpObj G] {g : ℕ}
    (f : (Fin g ⊕ Fin g → ℤ) →ₗ[ℤ] D.La) (n d L : ℕ) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over Y) ⟶ G))
    (χ : o₀.A ⟶ G) (ψ : D.La → (𝟙_ (Over Y) ⟶ G)) (T : Over Y) (lv : D.La → (T ⟶ o₀.A)) : Prop :=
  (∀ x y, lv (x + y) = lv x * lv y) ∧ (∀ (c : D.O) x, lv (c • x) = lv x ≫ o₀.act.act c) ∧
    (∀ x, lv (L • x) = 1) ∧ (∀ a, toUnit T ≫ lev a = (lv (f a) ^ d) ≫ χ) ∧
    (∀ y, (lv y ^ (d * n)) ≫ χ = toUnit T ≫ ψ y) ∧
    ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ T.left) (β : R →+* κ), x ≫ T.hom ≫ s = spMap β →
      ∃ I : TateIsoO D κ (Over.mk (x ≫ T.hom) ⟶ o₀.A) (fun c g' => g' ≫ o₀.act.act c)
          (fun m g₁ g₂ z => Out.WeilIs o₀.A (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) m g₁ g₂ (unitOn z)),
        ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv y = I.ev L y

end GlobalTheory.UPel.HT
