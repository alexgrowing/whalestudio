import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type}

abbrev SmallCat (W : K → X.left.Opens) : Type 1 := (IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).FullSubcategory

abbrev smallAt (W : K → X.left.Opens) {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) (h : Sm W x) :
    SmallCat W := ⟨trivAt x, h⟩

theorem Sm.map {W : K → X.left.Opens} {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') {x : Pt X D} (h : Sm W x) : Sm W (spOver φ ≫ x) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, (trivMap φ x).le_preimage hi⟩

open Classical in

def cocOf (W : K → X.left.Opens) (n : C1 ((IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _))) :
    Fn1 X := fun _ _ _ _ _ _ φ x ↦
  if h : Sm W x then n (smallAt W x h) (smallAt W _ (h.map φ)) (ObjectProperty.homMk (trivMap φ x)) else 0

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt
variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type}

theorem isCoc_cocOf (W : K → X.left.Opens)
    (n : C1 ((IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _)))
    (hn : ∀ (T T' T'' : SmallCat W) (a : T ⟶ T') (b : T' ⟶ T''), T.obj.J = ⊥ → T'.obj.J = ⊥ →
      T''.obj.J = ⊥ → d1 _ n T T' T'' a b = 0) : IsCoc W (cocOf W n) := by
  intro D _ _ D' _ _ D'' _ _ φ ψ x hx
  have tr : ∀ (y y' : Pt X D'') (e : y = y') (h : Sm W y) (h' : Sm W y')
      (f : smallAt W x hx ⟶ smallAt W y h) (f' : smallAt W x hx ⟶ smallAt W y' h'),
      (∀ r, f.hom.φ r = f'.hom.φ r) → n _ _ f = n _ _ f' := by
    rintro y _ rfl h h' f f' hf
    have : f = f' := ObjectProperty.hom_ext _ (Thick.hom_ext hf)
    subst this; rfl
  have key := hn (smallAt W x hx) (smallAt W _ (hx.map φ)) (smallAt W _ ((hx.map φ).map ψ))
    (ObjectProperty.homMk (trivMap φ x)) (ObjectProperty.homMk (trivMap ψ _)) rfl rfl rfl
  rw [d1_apply] at key
  simp only [cocOf, dif_pos hx, dif_pos (hx.map φ), dif_pos (hx.map (ψ.comp φ))]
  have e := tr (spOver (ψ.comp φ) ≫ x) (spOver ψ ≫ spOver φ ≫ x)
    (by rw [← spOver_comp, Category.assoc]) (hx.map (ψ.comp φ)) ((hx.map φ).map ψ)
    (ObjectProperty.homMk (trivMap (ψ.comp φ) x))
    ((ObjectProperty.homMk (trivMap φ x) : smallAt W x hx ⟶ smallAt W _ (hx.map φ)) ≫
      (ObjectProperty.homMk (trivMap ψ (spOver φ ≫ x)) : smallAt W _ (hx.map φ) ⟶ smallAt W _ ((hx.map φ).map ψ)))
    (fun _ ↦ rfl)
  rw [e]
  change ψ _ - _ + _ = 0 at key
  linear_combination -key
end GlobalTheory.PtExt
