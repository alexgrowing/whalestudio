import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Vert.Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Hom.map_genericPoint {Z Z₁ : Model O} (f : Hom Z₁ Z) :
    f.f (genericPoint Z₁.X) = genericPoint Z.X := by
  have := (genericPoint_spec Z₁.X).image f.f.continuous
  rw [Set.image_univ, f.f.surjective.range_eq, closure_univ] at this
  exact this.eq (genericPoint_spec Z.X)

abbrev fnFld (Z : Model O) : Type := Z.X.residueField (genericPoint Z.X)

def fnConst (Z : Model O) : O →+* Z.fnFld :=
  (Z.X.Γevaluation (genericPoint Z.X)).hom.comp (algebraMap O Γ(Z.X, ⊤))

def Hom.fnMap {Z Z₁ : Model O} (f : Hom Z₁ Z) : Z.fnFld →+* Z₁.fnFld :=
  ((Z.X.residueFieldCongr f.map_genericPoint).inv ≫ f.f.residueFieldMap (genericPoint Z₁.X)).hom

theorem residueFieldCongr_Γevaluation {X : Scheme.{0}} {x y : X} (e : x = y) (a : Γ(X, ⊤)) :
    (X.residueFieldCongr e).hom (X.Γevaluation x a) = X.Γevaluation y a := by
  subst e
  rfl

theorem Hom.fnMap_comp_fnConst {Z Z₁ : Model O} (f : Hom Z₁ Z) :
    f.fnMap.comp Z.fnConst = Z₁.fnConst := by
  ext g
  simp only [Hom.fnMap, fnConst, RingHom.comp_apply, CommRingCat.hom_comp,
    Scheme.residueFieldCongr_inv]
  rw [residueFieldCongr_Γevaluation, Scheme.Γevaluation_naturality_apply]
  exact congrArg _ (appTop_const f.comp_str g)

theorem fnConst_injective (Z : Model O) : Function.Injective Z.fnConst := by
  refine (injective_iff_map_eq_zero _).2 fun g hg => by_contra fun h0 => ?_
  have h1 : genericPoint Z.X ∈ Z.X.basicOpen (Z.const g) :=
    Z.gen_le_basicOpen h0 Z.genericPoint_mem_gen
  exact (Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ _ _).2 h1 hg

theorem Hom.fnMap_congr {Z Z₁ : Model O} {f f' : Hom Z₁ Z} (e : f.f = f'.f) :
    f.fnMap = f'.fnMap := by
  cases f
  cases f'
  cases e
  rfl

theorem residueFieldMap_comp_congr {X Y W : Scheme.{0}} (a : W ⟶ Y) (b : Y ⟶ X) (p₂ : W) (p₁ : Y)
    (p : X) (e₁ : a p₂ = p₁) (e : b p₁ = p) (e' : (a ≫ b) p₂ = p) :
    (X.residueFieldCongr e').inv ≫ (a ≫ b).residueFieldMap p₂ =
      ((X.residueFieldCongr e).inv ≫ b.residueFieldMap p₁) ≫
        (Y.residueFieldCongr e₁).inv ≫ a.residueFieldMap p₂ := by
  subst e₁ e
  simp

theorem Hom.fnMap_comp {Z Z₁ Z₂ : Model O} (g : Hom Z₂ Z₁) (f : Hom Z₁ Z) :
    (g.comp f).fnMap = g.fnMap.comp f.fnMap := by
  simp only [Hom.fnMap]
  rw [← CommRingCat.hom_comp]
  exact congrArg CommRingCat.Hom.hom (residueFieldMap_comp_congr g.f f.f _ _ _
    g.map_genericPoint f.map_genericPoint (g.comp f).map_genericPoint)

theorem Hom.fnMap_comp_eq {B B₁ B₂ Z : Model O} (f₁ : Hom B₁ B) (f₂ : Hom B₂ B) (h₁ : Hom Z B₁)
    (h₂ : Hom Z B₂) (w : h₁.f ≫ f₁.f = h₂.f ≫ f₂.f) :
    h₁.fnMap.comp f₁.fnMap = h₂.fnMap.comp f₂.fnMap := by
  rw [← Hom.fnMap_comp, ← Hom.fnMap_comp]
  exact Hom.fnMap_congr w

end GlobalTheory.Vert.Model
