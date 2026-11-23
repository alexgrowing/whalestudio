import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

universe w₁

def semilinearOfAdditive {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {M : Type w} {M' : Type w₁}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (τ : M →+ M')
    (h : ∀ (a : R) x, τ (a • x) = σ a • τ x) : M →ₛₗ[σ] M' where
  toFun := τ
  map_add' := map_add τ
  map_smul' := h

def semiMor {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {C : Type u} [Category.{v} C]
    (E : C ⥤ Type v') (F : C ⥤ ModuleCat.{w} R) (F' : C ⥤ ModuleCat.{w} R') (τ : ∀ A : C, F.obj A →+ F'.obj A)
    (hσ : ∀ A (a : R) x, τ A (a • x) = σ a • τ A x)
    (hn : ∀ {A B : C} (f : A ⟶ B) x, τ B ((F.map f).hom x) = (F'.map f).hom (τ A x)) :
    CH.Mor (CH.elF E F) (CH.elF E F') σ where
  G := 𝟭 _
  τ X := semilinearOfAdditive σ (τ X.1) (hσ X.1)
  nat φ x := hn φ.1 x

theorem d_aug_zero {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {M : Type w₁} [AddCommGroup M] [Module R M] (e : ∀ T : C, M →ₗ[R] F.obj T)
    (he : ∀ {T T' : C} (φ : T ⟶ T') x, (F.map φ).hom (e T x) = e T' x) (x : M) :
    CH.d F 0 (CH.aug F e x) = 0 := by
  funext s
  simp only [CH.d, LinearMap.coe_mk, AddHom.coe_mk, CH.aug, LinearMap.pi_apply, he]
  simp

theorem ptsAug_d {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F : C ⥤ ModuleCat.{w} R) (A : C) (x : F.obj A) :
    CH.d (CH.elF (CH.pts j A) (j ⋙ F)) 0 (CH.ptsAug j F A x) = 0 :=
  d_aug_zero _ _ (fun {X Y} φ y => by
    change (F.map (j.map φ.1)).hom ((F.map X.2).hom y) = (F.map Y.2).hom y
    rw [← ModuleCat.comp_apply, ← F.map_comp]
    exact congrArg (fun g => (F.map g).hom y) φ.2) x

theorem des_semi {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F : C ⥤ ModuleCat.{w} R) (F' : C ⥤ ModuleCat.{w} R') (τ : ∀ A : C, F.obj A →+ F'.obj A)
    (hσ : ∀ A (a : R) x, τ A (a • x) = σ a • τ A x) (hb : ∀ A, Function.Bijective (τ A))
    (hn : ∀ {A B : C} (f : A ⟶ B) x, τ B ((F.map f).hom x) = (F'.map f).hom (τ A x)) (s : R) :
    DesJ j F s ↔ DesJ j F' (σ s) := by
  refine forall_congr' fun A => ?_
  let m : CH.Mor (CH.elF (CH.pts j A) (j ⋙ F)) (CH.elF (CH.pts j A) (j ⋙ F')) σ :=
    semiMor σ (CH.pts j A) (j ⋙ F) (j ⋙ F') (fun X => τ (j.obj X)) (fun X => hσ _) (fun f x => hn (j.map f) x)
  refine CrystallineSemistableComparison.P.res_semilinear m.hom (CH.ptsAug j F A) (CH.ptsAug j F' A) (semilinearOfAdditive σ (τ A) (hσ A)) s (hb A)
    (fun n => ⟨?_, ?_⟩) (fun x => ?_)
  · intro f g h
    funext t
    have h' : τ (j.obj (t.obj (Fin.last n)).1) (f t) = τ (j.obj (t.obj (Fin.last n)).1) (g t) := congrFun h t
    exact (hb _).1 h'
  · intro g
    exact ⟨fun t => Function.surjInv (hb (j.obj (t.obj (Fin.last n)).1)).2 (g t),
      funext fun t => Function.surjInv_eq (hb (j.obj (t.obj (Fin.last n)).1)).2 (g t)⟩
  · funext t
    exact hn _ x

theorem des_res {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {C : Type u} [Category.{v} C] {T : Type u'}
    [Category.{v'} T] (j : T ⥤ C) (F : C ⥤ ModuleCat.{w} R') (s : R) :
    DesJ j (F ⋙ ModuleCat.restrictScalars σ) s ↔ DesJ j F (σ s) :=
  des_semi σ j (F ⋙ ModuleCat.restrictScalars σ) F (fun A => AddMonoidHom.id (F.obj A)) (fun _ _ _ => rfl)
    (fun _ => Function.bijective_id) (fun _ _ => rfl) s

def natRes {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (σ₁ : R →+* R₁) (σ₂ : R →+* R₂)
    {C : Type u} [Category.{v} C] (F₁ : C ⥤ ModuleCat.{w} R₁) (F₂ : C ⥤ ModuleCat.{w} R₂)
    (α : ∀ A : C, F₁.obj A →+ F₂.obj A) (hα : ∀ A (a : R) x, α A (σ₁ a • x) = σ₂ a • α A x)
    (nα : ∀ {A B : C} (f : A ⟶ B) x, α B ((F₁.map f).hom x) = (F₂.map f).hom (α A x)) :
    F₁ ⋙ ModuleCat.restrictScalars σ₁ ⟶ F₂ ⋙ ModuleCat.restrictScalars σ₂ where
  app A :=
    letI : Module R (F₁.obj A) := Module.compHom _ σ₁
    letI : Module R (F₂.obj A) := Module.compHom _ σ₂
    ModuleCat.ofHom {
      toFun := α A
      map_add' := map_add (α A)
      map_smul' := hα A }
  naturality A B f := by
    ext x
    exact nα f x

theorem des_ses_nat {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    {G₁ G₂ G₃ : C ⥤ ModuleCat.{w} R} (α : G₁ ⟶ G₂) (β : G₂ ⟶ G₃)
    (hi : ∀ A, Function.Injective (α.app A).hom) (he : ∀ A, Function.Exact (α.app A).hom (β.app A).hom)
    (hs : ∀ A, Function.Surjective (β.app A).hom) (s : R) :
    (DesJ j G₁ s → DesJ j G₃ s → DesJ j G₂ (s ^ 3)) ∧ (DesJ j G₂ s → DesJ j G₃ s → DesJ j G₁ (s ^ 3)) := by
  have key : ∀ A : C,
      ((CH.cx (CH.elF (CH.pts j A) (j ⋙ G₁))).ResUpTo s (CH.ptsAug j G₁ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₃))).ResUpTo s (CH.ptsAug j G₃ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₂))).ResUpTo (s ^ 3) (CH.ptsAug j G₂ A)) ∧
      ((CH.cx (CH.elF (CH.pts j A) (j ⋙ G₂))).ResUpTo s (CH.ptsAug j G₂ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₃))).ResUpTo s (CH.ptsAug j G₃ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₁))).ResUpTo (s ^ 3) (CH.ptsAug j G₁ A)) := by
    intro A
    let a := Functor.whiskerLeft (CategoryOfElements.π (CH.pts j A)) (Functor.whiskerLeft j α)
    let b := Functor.whiskerLeft (CategoryOfElements.π (CH.pts j A)) (Functor.whiskerLeft j β)
    obtain ⟨h1, h2, h3⟩ := CrystallineSemistableComparison.P.ses_cochains a b (fun X => hi _) (fun X => he _) (fun X => hs _)
    obtain ⟨k1, k2, -⟩ := CrystallineSemistableComparison.P.res_2of3 _ _ h1 h2 h3 (α.app A).hom (β.app A).hom (hi A) (he A) (hs A)
      (CH.ptsAug j G₁ A) (CH.ptsAug j G₂ A) (CH.ptsAug j G₃ A)
      (fun x => funext fun t => (congrArg (fun φ => ModuleCat.Hom.hom φ x) (α.naturality (t.obj (Fin.last 0)).2)).symm)
      (fun x => funext fun t => (congrArg (fun φ => ModuleCat.Hom.hom φ x) (β.naturality (t.obj (Fin.last 0)).2)).symm)
      (fun x => ptsAug_d j G₂ A x) s
    exact ⟨k1, k2⟩
  exact ⟨fun h1 h3 A => (key A).1 (h1 A) (h3 A), fun h2 h3 A => (key A).2 (h2 A) (h3 A)⟩

theorem des_ses {R R₁ R₂ R₃ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₃] (σ₁ : R →+* R₁) (σ₂ : R →+* R₂) (σ₃ : R →+* R₃)
    {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F₁ : C ⥤ ModuleCat.{w} R₁) (F₂ : C ⥤ ModuleCat.{w} R₂) (F₃ : C ⥤ ModuleCat.{w} R₃)
    (α : ∀ A : C, F₁.obj A →+ F₂.obj A) (β : ∀ A : C, F₂.obj A →+ F₃.obj A)
    (hα : ∀ A (a : R) x, α A (σ₁ a • x) = σ₂ a • α A x) (hβ : ∀ A (a : R) x, β A (σ₂ a • x) = σ₃ a • β A x)
    (nα : ∀ {A B : C} (f : A ⟶ B) x, α B ((F₁.map f).hom x) = (F₂.map f).hom (α A x))
    (nβ : ∀ {A B : C} (f : A ⟶ B) x, β B ((F₂.map f).hom x) = (F₃.map f).hom (β A x))
    (hi : ∀ A, Function.Injective (α A)) (he : ∀ A, Function.Exact (α A) (β A)) (hs : ∀ A, Function.Surjective (β A)) (s : R) :
    (DesJ j F₁ (σ₁ s) → DesJ j F₃ (σ₃ s) → DesJ j F₂ (σ₂ (s ^ 3))) ∧
    (DesJ j F₂ (σ₂ s) → DesJ j F₃ (σ₃ s) → DesJ j F₁ (σ₁ (s ^ 3))) := by
  have key := des_ses_nat j (natRes σ₁ σ₂ F₁ F₂ α hα nα) (natRes σ₂ σ₃ F₂ F₃ β hβ nβ)
    (fun A x y h => hi A h) (fun A y => he A y) (fun A y => hs A y) s
  refine ⟨fun h1 h3 => ?_, fun h2 h3 => ?_⟩
  · exact (des_res σ₂ j F₂ (s ^ 3)).1 (key.1 ((des_res σ₁ j F₁ s).2 h1) ((des_res σ₃ j F₃ s).2 h3))
  · exact (des_res σ₁ j F₁ (s ^ 3)).1 (key.2 ((des_res σ₂ j F₂ s).2 h2) ((des_res σ₃ j F₃ s).2 h3))

end CrystallineSemistableComparison.D
