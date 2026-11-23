import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {S : Scheme.{0}}

def transl {A : Over S} [GrpObj A] (h : 𝟙_ (Over S) ⟶ A) : A ⟶ A := 𝟙 A * (toUnit A ≫ h)

def lbPow {X : Scheme.{0}} (L : LB X) (m : ℕ) : LB X :=
  LB.LinComb L (K := Fin m) (fun _ => 𝟙 X) (fun _ => 1)

def sq2 {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    (G2 A).left ⟶ (G2 A').left :=
  (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem eta_zero {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)

theorem eta_neg {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (x : D.La) :
    o.eta (-x) = (o.eta x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← o.eta_add, add_neg_cancel, eta_zero]

def heckeSub {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (g : D.La →ₗ[D.O] D.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • g x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add, smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

theorem mem_heckeSub {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (g : D.La →ₗ[D.O] D.La) (N : ℕ)
    (x : D.La) : o.eta (N • g x) ∈ heckeSub o g N := ⟨x, rfl⟩

theorem one_comp_transl {A : Over S} [GrpObj A] (h : 𝟙_ (Over S) ⟶ A) : (1 : 𝟙_ (Over S) ⟶ A) ≫ transl h = h := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (1 ≫ toUnit A) (𝟙 _),
    Category.id_comp, _root_.one_mul]

theorem comp_eq_one_of_transl {A A' : Over S} [GrpObj A] [GrpObj A'] (ψ : A ⟶ A') [IsMonHom ψ]
    (h : 𝟙_ (Over S) ⟶ A) (hh : (transl h).left ≫ ψ.left = ψ.left) : h ≫ ψ = 1 := by
  have e : transl h ≫ ψ = ψ := Over.OverMorphism.ext hh
  rw [← one_comp_transl h, Category.assoc, e, one_comp]

end GlobalTheory.UPel.HT.Hecke
