import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def LieAt (b : Base D R) {A : Over S} [GrpObj A] (act : OActN D.O A) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S) : Prop :=
  ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v →
    ∃ w : Fin D.a → (epsPtR x ⟶ A),
      (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧
      v = (List.ofFn w).prod

def LieRankAt (b : Base D R) {A : Over S} [GrpObj A] (act : OActN D.O A) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (g : R' →+* k) (i : Fin D.a),
    LieMult (act.toF D) (spMap g ≫ x) ((g.comp β).comp (b.t i)) D.m

def LieHer (b : Base D R) {A : Over S} [GrpObj A] (act : OActN D.O A) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S) : Prop :=
  ∀ (R'' : Type) [CommRing R''] (g : R' →+* R''),
    LieAt b act (g.comp β) (spMap g ≫ x) ∧ LieRankAt b act (g.comp β) (spMap g ≫ x)

end GlobalTheory.UPel.HT
