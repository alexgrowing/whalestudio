import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.SubsingletonOfSubsingletonFreeSheaf

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

universe w v u

noncomputable section

namespace GlobalTheory

variable {X : Scheme.{u}}

variable (X) in

def toAbSheaf : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance toAbSheaf_additive : (toAbSheaf X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

instance toAbSheaf_faithful : (toAbSheaf X).Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful

instance toAbSheaf_reflectsIsomorphisms : (toAbSheaf X).ReflectsIsomorphisms :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms

instance toAbSheaf_preservesFiniteLimits : PreservesFiniteLimits (toAbSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))

@[simp] lemma toAbSheaf_obj_obj (F : X.Modules) : ((toAbSheaf X).obj F).obj = F.presheaf := rfl

@[simp] lemma toAbSheaf_map_hom_app {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) :
    ((toAbSheaf X).map φ).hom.app (op U) = φ.app U := rfl

abbrev restrictGlobal (X : Scheme.{u}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom

lemma restrictGlobal_top (r : Γ(X, ⊤)) : restrictGlobal X ⊤ r = r := by
  have : (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ := rfl
  rw [restrictGlobal, this, op_id, X.presheaf.map_id]
  rfl

lemma map_restrictGlobal {U V : X.Opens} (i : V ⟶ U) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictGlobal X U r) = restrictGlobal X V r := by
  rw [restrictGlobal, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

def smulHom (F : X.Modules) (r : Γ(X, ⊤)) : F ⟶ F :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U ↦ F.smul (restrictGlobal X U.unop r)
      naturality := fun U V i ↦ by
        have := F.map_comp_smul i.unop (restrictGlobal X U.unop r)
        rw [map_restrictGlobal] at this
        exact this.symm }
    (fun U a m ↦ smul_comm (restrictGlobal X U.unop r) (show Γ(X, U.unop) from a) (show Γ(F, U.unop) from m))

@[simp] lemma smulHom_app_apply (F : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) (x : Γ(F, U)) :
    (smulHom F r).app U x = restrictGlobal X U r • x := rfl

@[simp] lemma smulHom_one (F : X.Modules) : smulHom F 1 = 𝟙 F := by
  ext U x; rw [smulHom_app_apply, map_one, one_smul]; rfl

@[simp] lemma smulHom_zero (F : X.Modules) : smulHom F 0 = 0 := by
  ext U x; rw [smulHom_app_apply, map_zero, zero_smul]; rfl

lemma smulHom_add (F : X.Modules) (r s : Γ(X, ⊤)) :
    smulHom F (r + s) = smulHom F r + smulHom F s := by
  ext U x; rw [smulHom_app_apply, map_add, add_smul]; rfl

lemma smulHom_mul (F : X.Modules) (r s : Γ(X, ⊤)) :
    smulHom F (r * s) = smulHom F s ≫ smulHom F r := by
  ext U x; rw [smulHom_app_apply, map_mul, mul_smul]; rfl

@[reassoc] lemma smulHom_comp {F G : X.Modules} (φ : F ⟶ G) (r : Γ(X, ⊤)) :
    smulHom F r ≫ φ = φ ≫ smulHom G r := by
  ext U x
  exact φ.app_smul (restrictGlobal X U r) x

@[simps] def smulEnd (F : X.Modules) : Γ(X, ⊤) →+* End F where
  toFun := smulHom F
  map_one' := smulHom_one F
  map_mul' := smulHom_mul F
  map_zero' := smulHom_zero F
  map_add' := smulHom_add F

instance linearModules : Linear Γ(X, ⊤) X.Modules where
  homModule F G :=
    { smul r φ := φ ≫ smulHom G r
      one_smul φ := by change φ ≫ _ = _; rw [smulHom_one, Category.comp_id]
      mul_smul r s φ := by change φ ≫ _ = (φ ≫ _) ≫ _; rw [smulHom_mul, Category.assoc]
      smul_zero r := zero_comp
      smul_add r φ ψ := Preadditive.add_comp _ _ _ _ _ _
      add_smul r s φ := by
        change φ ≫ _ = φ ≫ _ + φ ≫ _; rw [smulHom_add, Preadditive.comp_add]
      zero_smul φ := by change φ ≫ _ = _; rw [smulHom_zero, comp_zero] }
  smul_comp F G H r φ ψ := by
    change (φ ≫ _) ≫ ψ = (φ ≫ ψ) ≫ _
    rw [Category.assoc, Category.assoc, smulHom_comp]
  comp_smul F G H φ r ψ := (Category.assoc _ _ _).symm

lemma smul_hom_def {F G : X.Modules} (r : Γ(X, ⊤)) (φ : F ⟶ G) : r • φ = φ ≫ smulHom G r := rfl

lemma smulHom_eq_smul_id (F : X.Modules) (r : Γ(X, ⊤)) : smulHom F r = r • 𝟙 F :=
  (Category.id_comp _).symm

@[simp] lemma smul_app_apply {F G : X.Modules} (r : Γ(X, ⊤)) (φ : F ⟶ G) (U : X.Opens)
    (x : Γ(F, U)) : (r • φ).app U x = restrictGlobal X U r • φ.app U x := rfl

@[reducible] def addCommGroupOfAction {A M : Type*} [CommRing A] (inst : AddCommGroup M)
    (ρ : A →+* AddMonoid.End M) : AddCommGroup M :=
  { inst with
    zsmul := fun n x ↦ ρ (algebraMap ℤ A n) x
    zsmul_zero' := fun x ↦ by
      change ρ (algebraMap ℤ A 0) x = 0
      rw [map_zero, map_zero]; rfl
    zsmul_succ' := fun n x ↦ by
      change ρ (algebraMap ℤ A (n + 1 : ℕ)) x = ρ (algebraMap ℤ A n) x + x
      rw [Nat.cast_succ, map_add, map_add, map_one, map_one]; rfl
    zsmul_neg' := fun n x ↦ by
      change ρ (algebraMap ℤ A (Int.negSucc n)) x = -ρ (algebraMap ℤ A (n + 1 : ℕ)) x
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) from rfl, map_neg, map_neg]; rfl }

def WithAction {A M : Type*} [CommRing A] [AddCommGroup M] (_ρ : A →+* AddMonoid.End M) := M

namespace WithAction

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [AddCommGroup N]
  (ρ : A →+* AddMonoid.End M) (σ : A →+* AddMonoid.End N)

instance instAddCommGroup : AddCommGroup (WithAction ρ) := addCommGroupOfAction (M := M) ‹_› ρ

def toBase : WithAction ρ ≃+ M where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl

variable (R : Type*) [CommRing R] [Algebra R A]

instance instModule : Module R (WithAction ρ) where
  smul r x := ρ (algebraMap R A r) x
  one_smul x := by
    change ρ (algebraMap R A 1) x = x
    rw [map_one, map_one]; rfl
  mul_smul r s x := by
    change ρ (algebraMap R A (r * s)) x = _
    rw [map_mul, map_mul]; rfl
  smul_zero r := map_zero (ρ (algebraMap R A r))
  smul_add r := map_add (ρ (algebraMap R A r))
  add_smul r s x := by
    change ρ (algebraMap R A (r + s)) x = _
    rw [map_add, map_add]; rfl
  zero_smul x := by
    change ρ (algebraMap R A 0) x = _
    rw [map_zero, map_zero]; rfl

example : instModule ρ ℤ = AddCommGroup.toIntModule (WithAction ρ) := by
  with_reducible_and_instances rfl

variable {R} in

lemma toBase_smul (r : R) (x : WithAction ρ) :
    toBase ρ (r • x) = ρ (algebraMap R A r) (toBase ρ x) := rfl

instance instIsScalarTower (S : Type*) [CommRing S] [Algebra S A] [Algebra R S]
    [IsScalarTower R S A] : IsScalarTower R S (WithAction ρ) :=
  .of_algebraMap_smul fun r x ↦ by
    apply (toBase ρ).injective
    rw [toBase_smul, toBase_smul, ← IsScalarTower.algebraMap_apply]

instance instSMulCommClass (S : Type*) [CommRing S] [Algebra S A] :
    SMulCommClass R S (WithAction ρ) where
  smul_comm r s x := by
    rw [← algebraMap_smul A r, ← algebraMap_smul A s, ← algebraMap_smul A r,
      ← algebraMap_smul A s (_ • x), smul_smul, smul_smul, mul_comm]

def linearMap (f : M →+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) :
    WithAction ρ →ₗ[R] WithAction σ where
  toFun := f
  map_add' := f.map_add
  map_smul' _ x := h _ x

lemma toBase_linearMap (f : M →+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) (x : WithAction ρ) :
    toBase σ (linearMap ρ σ R f h x) = f (toBase ρ x) := rfl

def linearEquiv (f : M ≃+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) :
    WithAction ρ ≃ₗ[R] WithAction σ where
  toFun := f
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv
  map_add' := f.map_add
  map_smul' _ x := h _ x

lemma toBase_linearEquiv (f : M ≃+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) (x : WithAction ρ) :
    toBase σ (linearEquiv ρ σ R f h x) = f (toBase ρ x) := rfl

end WithAction

@[simps] def functorEndRingHom {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (G : C ⥤ D) [G.Additive] (Y : C) : End Y →+* End (G.obj Y) where
  toFun f := G.map f
  map_one' := G.map_id Y
  map_mul' f g := G.map_comp g f
  map_zero' := G.map_zero Y Y
  map_add' _ _ := G.map_add

namespace SiteCoh

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  {F G H : Sheaf J AddCommGrpCat.{v}} {n : ℕ} {U V W : C}

lemma map_id_apply (x : F.H' n U) : map (𝟙 F) n U x = x := by
  simp only [map, CategoryTheory.Functor.map_id]; rfl

lemma map_comp_apply (f : F ⟶ G) (g : G ⟶ H) (x : F.H' n U) :
    map (f ≫ g) n U x = map g n U (map f n U x) := by
  simp only [map, Functor.map_comp]; rfl

lemma map_add_apply (f g : F ⟶ G) (x : F.H' n U) :
    map (f + g) n U x = map f n U x + map g n U x := by
  simp only [map, Functor.map_add]; rfl

lemma map_zero_apply (x : F.H' n U) : map (0 : F ⟶ G) n U x = 0 := by
  simp only [map, Functor.map_zero]; rfl

lemma res_id_apply (x : F.H' n U) : res F n (𝟙 U) x = x := by
  simp only [res, op_id, CategoryTheory.Functor.map_id]; rfl

lemma res_comp_apply (i : V ⟶ U) (j : W ⟶ V) (x : F.H' n U) :
    res F n (j ≫ i) x = res F n j (res F n i x) := by
  simp only [res, op_comp, Functor.map_comp]; rfl

lemma res_map_apply (f : F ⟶ G) (i : V ⟶ U) (x : F.H' n U) :
    res G n i (map f n U x) = map f n V (res F n i x) :=
  (ConcreteCategory.congr_hom
    (((Sheaf.cohomologyPresheafFunctor J n).map f).naturality i.op) x).symm

variable (F n U) in

def endAction : End F →+* AddMonoid.End (F.H' n U) where
  toFun f := (map f n U).hom
  map_one' := AddMonoidHom.ext map_id_apply
  map_mul' f g := AddMonoidHom.ext (map_comp_apply g f)
  map_zero' := AddMonoidHom.ext map_zero_apply
  map_add' f g := AddMonoidHom.ext (map_add_apply f g)

lemma endAction_apply (f : End F) (x : F.H' n U) : endAction F n U f x = map f n U x := rfl

end SiteCoh

end GlobalTheory
