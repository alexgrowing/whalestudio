import Mathlib

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

abbrev Shv : Type 2 := Sheaf (Scheme.proetaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))

omit [TopologicalSpace R] [IsTopologicalRing R] in
instance : HasSheafify (Scheme.proetaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

omit [TopologicalSpace R] [IsTopologicalRing R] in
instance : IsGrothendieckAbelian.{1} (Shv R) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} (ULift.{1} R))

def coefPre : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (ULift.{1} C(U.unop, R))
  map {U V} f := ModuleCat.ofHom
    { toFun := fun g => ⟨g.down.comp f.unop.base.hom⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def coef : Shv R := (presheafToSheaf _ _).obj (coefPre R)

def freeOn : Scheme.{0} ⥤ Shv R :=
  uliftYoneda.{1} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R)) ⋙ presheafToSheaf _ _

abbrev HS (F : Shv R) (n : ℕ) (X : Scheme.{0}) : Type 1 := Abelian.Ext.{1} ((freeOn R).obj X) F n

def H (n : ℕ) (X : Scheme.{0}) : Type 1 := HS R (coef R) n X

instance (n : ℕ) (X : Scheme.{0}) : AddCommGroup (H R n X) := inferInstanceAs (AddCommGroup (HS R (coef R) n X))

instance (n : ℕ) (X : Scheme.{0}) : Module R (H R n X) :=
  Module.compHom (HS R (coef R) n X) (ULift.ringEquiv.symm : R ≃+* ULift.{1} R).toRingHom

def pull (n : ℕ) {X Y : Scheme.{0}} (f : X ⟶ Y) : H R n Y →ₗ[R] H R n X where
  toFun x := (Abelian.Ext.mk₀ ((freeOn R).map f)).comp (x : HS R (coef R) n Y) (zero_add n)
  map_add' x y := Abelian.Ext.comp_add _ _ _ _
  map_smul' r x := Abelian.Ext.comp_smul _ _ _ (ULift.up r : ULift.{1} R)

theorem pull_id (n : ℕ) (X : Scheme.{0}) : pull R n (𝟙 X) = LinearMap.id := by
  ext x
  change (Abelian.Ext.mk₀ ((freeOn R).map (𝟙 X))).comp (x : HS R (coef R) n X) (zero_add n) = x
  rw [CategoryTheory.Functor.map_id]
  exact Abelian.Ext.mk₀_id_comp _

theorem pull_comp (n : ℕ) {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull R n (f ≫ g) = (pull R n f).comp (pull R n g) := by
  ext x
  change (Abelian.Ext.mk₀ ((freeOn R).map (f ≫ g))).comp (x : HS R (coef R) n Z) (zero_add n) =
    (Abelian.Ext.mk₀ ((freeOn R).map f)).comp ((Abelian.Ext.mk₀ ((freeOn R).map g)).comp (x : HS R (coef R) n Z) (zero_add n)) (zero_add n)
  rw [Functor.map_comp]
  exact (Abelian.Ext.mk₀_comp_mk₀_assoc _ _ _).symm

section Galois

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

abbrev geom : Scheme.{0} := pullback p (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

def galMap (σ : Ω ≃ₐ[k] Ω) : geom Ω p ⟶ geom Ω p :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    congr 3
    ext x
    simp)

@[reassoc] theorem galMap_fst (σ : Ω ≃ₐ[k] Ω) : galMap Ω p σ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc] theorem galMap_snd (σ : Ω ≃ₐ[k] Ω) :
    galMap Ω p σ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) := pullback.lift_snd _ _ _

def geomMap {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y) (hu : u ≫ q = p) : geom Ω p ⟶ geom Ω q :=
  pullback.lift (pullback.fst _ _ ≫ u) (pullback.snd _ _) (by rw [Category.assoc, hu, pullback.condition])

def gal (n : ℕ) : Representation R (Ω ≃ₐ[k] Ω) (H R n (geom Ω p)) where
  toFun σ := pull R n (galMap Ω p σ)
  map_one' := by
    have : galMap Ω p 1 = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [galMap_fst, Category.id_comp]
      · have h : CommRingCat.ofHom ((1 : Ω ≃ₐ[k] Ω) : Ω →+* Ω) = 𝟙 _ := by ext x; rfl
        rw [galMap_snd, h, Spec.map_id, Category.id_comp, Category.comp_id]
    rw [this, pull_id]; rfl
  map_mul' σ τ := by
    have : galMap Ω p (σ * τ) = galMap Ω p σ ≫ galMap Ω p τ := by
      apply pullback.hom_ext
      · rw [Category.assoc, galMap_fst, galMap_fst, galMap_fst]
      · have h : CommRingCat.ofHom ((σ * τ : Ω ≃ₐ[k] Ω) : Ω →+* Ω) =
            CommRingCat.ofHom (τ : Ω →+* Ω) ≫ CommRingCat.ofHom (σ : Ω →+* Ω) := by ext x; rfl
        rw [Category.assoc, galMap_snd, galMap_snd, galMap_snd_assoc, h, Spec.map_comp]
    rw [this, pull_comp]; rfl

def IsMatrixForm (n : ℕ) {S : Type} [CommRing S] [Algebra R S] {a : ℕ} (r : (Ω ≃ₐ[k] Ω) →* GL (Fin a) S) : Prop :=
  ∃ b : Module.Basis (Fin a) R (H R n (geom Ω p)), ∀ σ,
    (r σ : Matrix (Fin a) (Fin a) S) = (LinearMap.toMatrix b b (gal R Ω p n σ)).map (algebraMap R S)

end Galois

abbrev fibre {O K : Type} [CommRing O] [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) (φ : O →+* K) : Scheme.{0} :=
  pullback p (Spec.map (CommRingCat.ofHom φ))

end GlobalTheory.Et

end
