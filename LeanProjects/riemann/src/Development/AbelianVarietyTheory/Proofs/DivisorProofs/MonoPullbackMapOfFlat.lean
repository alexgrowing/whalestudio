import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsLocalizedModuleGermLinearPointOfPrime

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.SkyMod

variable {X : Scheme.{u}} (x : X)

def Obj (U : X.Opens) (M : Type u) : Type u := PLift (x ∈ U) → M

instance (U : X.Opens) (M : Type u) [AddCommGroup M] : AddCommGroup (Obj x U M) :=
  inferInstanceAs (AddCommGroup (PLift (x ∈ U) → M))

instance (U : X.Opens) (M : Type u) [AddCommGroup M] [Module (X.presheaf.stalk x) M] :
    SMul Γ(X, U) (Obj x U M) where
  smul r m := fun h ↦ X.presheaf.germ U x h.down r • m h

instance (U : X.Opens) (M : Type u) [AddCommGroup M] [Module (X.presheaf.stalk x) M] :
    Module Γ(X, U) (Obj x U M) where
  one_smul m := funext fun h ↦ show X.presheaf.germ U x h.down 1 • m h = m h by simp
  mul_smul r s m := funext fun h ↦ show X.presheaf.germ U x h.down (r * s) • m h =
    X.presheaf.germ U x h.down r • X.presheaf.germ U x h.down s • m h by simp [mul_smul]
  smul_zero r := funext fun h ↦ smul_zero (X.presheaf.germ U x h.down r)
  smul_add r m n := funext fun h ↦ smul_add (X.presheaf.germ U x h.down r) (m h) (n h)
  add_smul r s m := funext fun h ↦ show X.presheaf.germ U x h.down (r + s) • m h =
    X.presheaf.germ U x h.down r • m h + X.presheaf.germ U x h.down s • m h by simp [add_smul]
  zero_smul m := funext fun h ↦ show X.presheaf.germ U x h.down 0 • m h = 0 by simp

variable (M : ModuleCat.{u} (X.presheaf.stalk x))

def skyPresheaf : (X.Opens)ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (Obj x U.unop M)
  map f := AddCommGrpCat.ofHom
    { toFun := fun m h ↦ m ⟨leOfHom f.unop h.down⟩, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }

instance (U : (X.Opens)ᵒᵖ) : Module (X.ringCatSheaf.val.obj U) ((skyPresheaf x M).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (Obj x U.unop M))

def skyPresheafOfModules : PresheafOfModules.{u} X.ringCatSheaf.val :=
  PresheafOfModules.ofPresheaf (skyPresheaf x M) fun U V f r m ↦ funext fun h ↦ by
    have e := X.presheaf.germ_res_apply f.unop x h.down (r : Γ(X, U.unop))
    exact congrArg (· • m ⟨leOfHom f.unop h.down⟩) e.symm

theorem skyPresheaf_isSheaf : TopCat.Presheaf.IsSheaf (X := X.toTopCat) (skyPresheaf x M) := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).2 fun ι U sf hsf ↦ ?_
  have key : ∀ i j (hi : x ∈ U i) (hj : x ∈ U j), sf i ⟨hi⟩ = sf j ⟨hj⟩ := fun i j hi hj ↦
    congrFun (hsf i j) ⟨⟨hi, hj⟩⟩
  refine ⟨fun h ↦ sf (Opens.mem_iSup.mp h.down).choose ⟨(Opens.mem_iSup.mp h.down).choose_spec⟩,
    fun i ↦ funext fun h ↦ key _ _ _ _, fun t ht ↦ funext fun h ↦ ?_⟩
  have := congrFun (ht (Opens.mem_iSup.mp h.down).choose) ⟨(Opens.mem_iSup.mp h.down).choose_spec⟩
  exact this

def sky : X.Modules where
  val := skyPresheafOfModules x M
  isSheaf := skyPresheaf_isSheaf x M

variable {x} in

def skyPresheafMap {M N : ModuleCat.{u} (X.presheaf.stalk x)} (g : M ⟶ N) :
    skyPresheaf x M ⟶ skyPresheaf x N where
  app U := AddCommGrpCat.ofHom
    { toFun := fun m h ↦ g (m h), map_zero' := funext fun _ ↦ map_zero g.hom,
      map_add' := fun m n ↦ funext fun h ↦ map_add g.hom (m h) (n h) }

def skyFunctor : ModuleCat.{u} (X.presheaf.stalk x) ⥤ X.Modules where
  obj M := sky x M
  map {M N} g := ⟨PresheafOfModules.homMk (M₁ := skyPresheafOfModules x M)
    (M₂ := skyPresheafOfModules x N) (skyPresheafMap g)
    fun U r m ↦ funext fun h ↦ g.hom.map_smul _ (m h)⟩

@[simp]
theorem skyFunctor_map_app {M N : ModuleCat.{u} (X.presheaf.stalk x)} (g : M ⟶ N) (U : X.Opens)
    (m : Γ(sky x M, U)) (h : PLift (x ∈ U)) :
    ((skyFunctor x).map g).app U m h = g (m h) := rfl

@[simp]
theorem sky_map_apply {U V : X.Opens} (i : V ⟶ U) (m : Γ(sky x M, U)) (h : PLift (x ∈ V)) :
    (sky x M).presheaf.map i.op m h = m ⟨leOfHom i h.down⟩ := rfl

def stalkFunctor : X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) where
  obj F := ModuleCat.of _ (F.presheaf.stalk x)
  map φ := ModuleCat.ofHom (GlobalTheory.QCoh.stalkLinear φ x)
  map_id F := by ext1; exact GlobalTheory.QCoh.stalkLinear_id F x
  map_comp φ ψ := by ext1; exact GlobalTheory.QCoh.stalkLinear_comp φ ψ x

@[simp]
theorem stalkFunctor_map {F G : X.Modules} (φ : F ⟶ G) :
    (stalkFunctor x).map φ = ModuleCat.ofHom (GlobalTheory.QCoh.stalkLinear φ x) := rfl

end GlobalTheory.SkyMod

namespace GlobalTheory.SkyMod

variable {X : Scheme.{u}} (x : X)

def unitApp (F : X.Modules) : F ⟶ sky x (ModuleCat.of _ (F.presheaf.stalk x)) :=
  ⟨PresheafOfModules.homMk (M₁ := F.val)
    (M₂ := skyPresheafOfModules x (ModuleCat.of _ (F.presheaf.stalk x)))
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun s h ↦ F.presheaf.germ U.unop x h.down s
          map_zero' := funext fun h ↦ map_zero _
          map_add' := fun s t ↦ funext fun h ↦ map_add _ s t }
      naturality := fun U V i ↦ by
        ext s
        funext h
        exact F.presheaf.germ_res_apply i.unop x h.down s }
    (fun U r s ↦ funext fun h ↦ GlobalTheory.QCoh.germ_smul F x h.down r s)⟩

@[simp]
theorem unitApp_app (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) (h : PLift (x ∈ U)) :
    (unitApp x F).app U s h = F.presheaf.germ U x h.down s := rfl

def counitAb (M : ModuleCat.{u} (X.presheaf.stalk x)) :
    (sky x M).presheaf.stalk x ⟶ AddCommGrpCat.of M :=
  colimit.desc _ (Cocone.mk (AddCommGrpCat.of M)
    { app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.mk' (M := Obj x U.unop.1 M)
        (fun m ↦ m ⟨U.unop.2⟩) fun _ _ ↦ rfl)
      naturality := fun U V i ↦ rfl })

theorem counitAb_germ (M : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U)
    (m : Γ(sky x M, U)) : counitAb x M ((sky x M).presheaf.germ U x hx m) = m ⟨hx⟩ := by
  rw [TopCat.Presheaf.germ, counitAb]
  erw [colimit.ι_desc_apply]
  rfl

end GlobalTheory.SkyMod

namespace GlobalTheory.SkyMod

variable {X : Scheme.{u}} (x : X)

def counitApp (M : ModuleCat.{u} (X.presheaf.stalk x)) :
    (stalkFunctor x).obj (sky x M) ⟶ M :=
  ModuleCat.ofHom
    { toFun := counitAb x M
      map_add' := map_add (counitAb x M).hom
      map_smul' := fun r t ↦ by
        obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hV, s, rfl⟩ := (sky x M).presheaf.exists_germ_eq t
        have hx : x ∈ U ⊓ V := ⟨hU, hV⟩
        rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) x hx,
          ← (sky x M).presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) x hx,
          RingHom.id_apply, ← GlobalTheory.QCoh.germ_smul, counitAb_germ, counitAb_germ]
        rfl }

@[simp]
theorem counitApp_germ (M : ModuleCat.{u} (X.presheaf.stalk x)) (U : X.Opens) (hx : x ∈ U)
    (m : Γ(sky x M, U)) : counitApp x M ((sky x M).presheaf.germ U x hx m) = m ⟨hx⟩ :=
  counitAb_germ x M U hx m

def adjunction : stalkFunctor x ⊣ skyFunctor x :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := unitApp x
          naturality := fun F G φ ↦ by
            refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
            ext s
            funext h
            exact (GlobalTheory.QCoh.stalkLinear_germ φ x h.down s).symm }
      counit :=
        { app := counitApp x
          naturality := fun M N g ↦ by
            ext t
            obtain ⟨V, hV, s, rfl⟩ := (sky x M).presheaf.exists_germ_eq t
            exact (congrArg (counitApp x N) (GlobalTheory.QCoh.stalkLinear_germ ((skyFunctor x).map g) x hV s)).trans
              ((counitApp_germ x N V hV _).trans (congrArg g (counitApp_germ x M V hV s)).symm) }
      left_triangle := by
        ext F : 2
        ext t
        obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
        change counitApp x _ (GlobalTheory.QCoh.stalkLinear (unitApp x F) x _) = _
        rw [GlobalTheory.QCoh.stalkLinear_germ, counitApp_germ]
        rfl
      right_triangle := by
        ext M : 2
        refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
        ext m
        funext h
        exact counitApp_germ x M U h.down m }

end GlobalTheory.SkyMod

theorem GlobalTheory.SkyMod.nonempty_adjunction : ∀ (X : Scheme.{0}) (x : X), Nonempty (GlobalTheory.SkyMod.stalkFunctor x ⊣ GlobalTheory.SkyMod.skyFunctor x) := fun _ x ↦ ⟨GlobalTheory.SkyMod.adjunction x⟩

open GlobalTheory.SkyMod in

theorem GlobalTheory.SkyMod.nonempty_sky_pushforward_iso : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (x : X), Nonempty (GlobalTheory.SkyMod.skyFunctor x ⋙ Scheme.Modules.pushforward f ≅ ModuleCat.restrictScalars (f.stalkMap x).hom ⋙ GlobalTheory.SkyMod.skyFunctor (f x)) := by
  intro X Y f x
  have key : ∀ (M : ModuleCat.{0} (X.presheaf.stalk x)) (U : Y.Opens) (r : Γ(Y, U))
      (m : Obj x (f ⁻¹ᵁ U) M) (h : PLift (f x ∈ U)),
      X.presheaf.germ (f ⁻¹ᵁ U) x h.down (f.app U r) • m h =
        f.stalkMap x (Y.presheaf.germ U (f x) h.down r) • m h := fun M U r m h ↦ by
    rw [Scheme.Hom.germ_stalkMap_apply]
  refine ⟨NatIso.ofComponents (fun M ↦ ⟨⟨PresheafOfModules.homMk (𝟙 _)
      (fun U r m ↦ funext fun h ↦ key M U.unop r m h)⟩,
    ⟨PresheafOfModules.homMk (𝟙 _) (fun U r m ↦ funext fun h ↦ (key M U.unop r m h).symm)⟩,
    rfl, rfl⟩) (fun g ↦ rfl)⟩

open GlobalTheory.SkyMod in

theorem GlobalTheory.mono_pullback_map_of_flat : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [Flat f] (G G' : Y.Modules)
    (φ : G ⟶ G') [Mono φ], Mono ((Scheme.Modules.pullback f).map φ) := by
  intro X Y f _ G G' φ _
  rw [GlobalTheory.QCoh.mono_iff_stalkLinear_injective]
  intro x
  obtain ⟨a₁⟩ := GlobalTheory.SkyMod.nonempty_adjunction X x
  obtain ⟨a₂⟩ := GlobalTheory.SkyMod.nonempty_adjunction Y (f x)
  obtain ⟨e⟩ := GlobalTheory.SkyMod.nonempty_sky_pushforward_iso X Y f x
  let adjA := ((Scheme.Modules.pullbackPushforwardAdjunction f).comp a₁).ofNatIsoRight e
  let adjB := a₂.comp (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)
  let iso := adjA.leftAdjointUniq adjB
  have hn := iso.hom.naturality φ
  have hφ : Function.Injective (GlobalTheory.QCoh.stalkLinear φ (f x)) := GlobalTheory.QCoh.stalkLinear_injective φ (f x)
  letI := (f.stalkMap x).hom.toAlgebra
  haveI : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have hext : Function.Injective ((ModuleCat.extendScalars (f.stalkMap x).hom).map
      ((stalkFunctor (f x)).map φ)) := by
    change Function.Injective (LinearMap.baseChange _ (GlobalTheory.QCoh.stalkLinear φ (f x)))
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hφ
  have h2 : Function.Injective (((Functor.comp (Scheme.Modules.pullback f) (stalkFunctor x)).map φ ≫
      iso.hom.app G').hom) := by
    rw [hn, ModuleCat.hom_comp, LinearMap.coe_comp]
    exact hext.comp (iso.app G).toLinearEquiv.injective
  rw [ModuleCat.hom_comp, LinearMap.coe_comp] at h2
  exact Function.Injective.of_comp h2
