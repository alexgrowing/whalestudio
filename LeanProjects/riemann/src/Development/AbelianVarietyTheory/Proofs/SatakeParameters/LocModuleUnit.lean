import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

variable {R : Type} [CommRing R]

def locModule (N : Submonoid (ULift.{1} R)) : ModuleCat.{1} (ULift.{1} R) ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj A := ModuleCat.of (ULift.{1} R) (LocalizedModule N A)
  map f := ModuleCat.ofHom
    (IsLocalizedModule.map N (LocalizedModule.mkLinearMap N _) (LocalizedModule.mkLinearMap N _) f.hom)
  map_id A := by
    ext x
    induction x using LocalizedModule.induction_on with
    | h a s => simp [IsLocalizedModule.map_LocalizedModules]
  map_comp f g := by
    ext x
    induction x using LocalizedModule.induction_on with
    | h a s => simp [IsLocalizedModule.map_LocalizedModules]

def locModuleUnit (N : Submonoid (ULift.{1} R)) : 𝟭 (ModuleCat.{1} (ULift.{1} R)) ⟶ locModule N where
  app A := ModuleCat.ofHom (LocalizedModule.mkLinearMap N A)
  naturality A B f := by
    ext x
    exact (LinearMap.congr_fun (IsLocalizedModule.map_comp N (LocalizedModule.mkLinearMap N A)
      (LocalizedModule.mkLinearMap N B) f.hom) x).symm

def loc (N : Submonoid (ULift.{1} R)) : Shv R ⥤ Shv R :=
  sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj (locModule N) ⋙ presheafToSheaf _ _

def locUnit (N : Submonoid (ULift.{1} R)) : 𝟭 (Shv R) ⟶ loc N where
  app F := ⟨Functor.whiskerLeft F.obj (locModuleUnit N) ≫ toSheafify _ (F.obj ⋙ locModule N)⟩
  naturality F G f := by
    apply Sheaf.hom_ext
    change f.hom ≫ Functor.whiskerLeft G.obj (locModuleUnit N) ≫ toSheafify _ (G.obj ⋙ locModule N) =
      (Functor.whiskerLeft F.obj (locModuleUnit N) ≫ toSheafify _ (F.obj ⋙ locModule N)) ≫
        sheafifyMap _ (Functor.whiskerRight f.hom (locModule N))
    have h : f.hom ≫ Functor.whiskerLeft G.obj (locModuleUnit N) =
        Functor.whiskerLeft F.obj (locModuleUnit N) ≫ Functor.whiskerRight f.hom (locModule N) := by
      ext U : 2
      exact (locModuleUnit N).naturality (f.hom.app U)
    rw [Category.assoc, ← toSheafify_naturality _ (Functor.whiskerRight f.hom (locModule N)), reassoc_of% h]

def HSmap {F F' : Shv R} (g : F ⟶ F') (n : ℕ) (X : Scheme.{0}) : HS R F n X →ₗ[ULift.{1} R] HS R F' n X where
  toFun x := x.comp (Abelian.Ext.mk₀ g) (add_zero n)
  map_add' x y := Abelian.Ext.add_comp _ _ _ _
  map_smul' r x := Abelian.Ext.smul_comp _ _ _ r

instance (N : Submonoid (ULift.{1} R)) : (locModule N).Additive where
  map_add {A B f g} := by
    apply ModuleCat.hom_ext
    simp only [locModule, ModuleCat.hom_add, ModuleCat.hom_ofHom, map_add]
    rfl

instance (N : Submonoid (ULift.{1} R)) : (loc N).Additive := by
  unfold loc; infer_instance

end GlobalTheory.Et

end
