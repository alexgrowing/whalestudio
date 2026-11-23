import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoCechComplexMapPresheafCubeRes
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexExactAtOfIsLocalizedModuleRes

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe t v u

noncomputable section

namespace GlobalTheory

variable {X Y : Scheme.{u}} {ι : Type}

section Basic

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

@[simps]
def sectionsPresheafMap {F G : X.Modules} (φ : F ⟶ G) :
    sectionsPresheaf R F ⟶ sectionsPresheaf R G where
  app W := ModuleCat.ofHom (sectionsOn.map R φ W.unop)
  naturality _ _ i := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (sectionsOn.res_map R φ i.unop.le x).symm)

theorem presheafRes_sectionsPresheaf (F : X.Modules) {W W' : X.Opens} (h : W' ≤ W) :
    presheafRes (sectionsPresheaf R F) h = sectionsOn.res R F h := rfl

theorem isSheaf_sectionsPresheaf (F : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (sectionsPresheaf R F) :=
  (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := ModuleCat.{u} R)
    (X := X.toPresheafedSpace.carrier) (sectionsPresheaf R F)).2
    ((TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := AddCommGrpCat.{u}) F.presheaf).1
      F.isSheaf)

@[simp]
theorem sectionsOn.res_res (F : X.Modules) {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (x : sectionsOn F W) :
    sectionsOn.res R F h' (sectionsOn.res R F h x) = sectionsOn.res R F (h'.trans h) x :=
  LinearMap.congr_fun (sectionsOn.res_comp_res R F h h') x

def sectionsOn.congrOpens (F : X.Modules) {W W' : X.Opens} (h : W = W') :
    sectionsOn F W ≃ₗ[R] sectionsOn F W' :=
  presheafCongr (sectionsPresheaf R F) h

@[simp]
theorem sectionsOn.congrOpens_apply (F : X.Modules) {W W' : X.Opens} (h : W = W')
    (x : sectionsOn F W) : sectionsOn.congrOpens R F h x = sectionsOn.res R F h.ge x := rfl

@[simp]
theorem sectionsOn.congrOpens_symm_apply (F : X.Modules) {W W' : X.Opens} (h : W = W')
    (x : sectionsOn F W') :
    (sectionsOn.congrOpens R F h).symm x = sectionsOn.res R F h.le x := rfl

variable (F : X.Modules) {G H : X.Modules} (V : X.Opens) (U : ι → X.Opens)

def cechCube : Cube.{u} ι R := presheafCube (sectionsPresheaf R F) V U

theorem cechCube_def : cechCube R F V U = presheafCube (sectionsPresheaf R F) V U := rfl

theorem cechCube_obj (s : Finset ι) :
    (cechCube R F V U).obj s = ModuleCat.of R (sectionsOn F (V ⊓ ⨅ i ∈ s, U i)) := rfl

theorem cechCube_obj' (s : Finset ι) :
    (cechCube R F V U).obj s = ModuleCat.of R (sectionsOn F (cechOpen V U s)) := rfl

theorem res_cechCube {s t : Finset ι} (h : s ⊆ t) :
    Cube.res (cechCube R F V U) h = sectionsOn.res R F (cechOpen_anti V U h) := rfl

variable {F} in

def cechCubeMap (φ : F ⟶ G) : cechCube R F V U ⟶ cechCube R G V U :=
  presheafCubeMap V U (sectionsPresheafMap R φ)

variable {F} in

@[simp]
theorem cechCubeMap_app (φ : F ⟶ G) (s : Finset ι) :
    ((cechCubeMap R V U φ).app s).hom = sectionsOn.map R φ (cechOpen V U s) := rfl

@[simps]
def cechCubeFunctor : X.Modules ⥤ Cube.{u} ι R where
  obj F := cechCube R F V U
  map := cechCubeMap R V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance cechCubeFunctor_additive : (cechCubeFunctor R V U).Additive where
  map_add := rfl

theorem cechCubeMap_smulHom (r : R) :
    cechCubeMap R V U (smulHom F (algebraMap R Γ(X, ⊤) r)) = r • 𝟙 (cechCube R F V U) := rfl

def cechCubeEmptyEquiv : sectionsOn F V ≃ₗ[R] (cechCube R F V U).obj ∅ :=
  presheafCubeEmptyEquiv (sectionsPresheaf R F) V U

theorem cechCubeEmptyEquiv_apply (x : sectionsOn F V) :
    cechCubeEmptyEquiv R F V U x = sectionsOn.res R F (cechOpen_le V U ∅) x := rfl

variable {V U} in

def cechCubeRes {V' : X.Opens} {U' : ι → X.Opens} (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) :
    cechCube R F V U ⟶ cechCube R F V' U' :=
  presheafCubeRes (sectionsPresheaf R F) h

variable {V U} in

@[simp]
theorem cechCubeRes_app {V' : X.Opens} {U' : ι → X.Opens}
    (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) (s : Finset ι) :
    ((cechCubeRes R F h).app s).hom = sectionsOn.res R F (h s) := rfl

def cechRestrictions : sectionsOn F V →ₗ[R] Cube.Term (cechCube R F V U) 1 :=
  presheafCechAug (sectionsPresheaf R F) V U

@[simp]
theorem cechRestrictions_apply (x : sectionsOn F V) (s : {s : Finset ι // s.card = 1}) :
    cechRestrictions R F V U x s = sectionsOn.res R F (cechOpen_le V U s.1) x := rfl

variable [LinearOrder ι]

def cech : CochainComplex (ModuleCat.{u} R) ℕ := cechComplex (cechCube R F V U)

def cechH (n : ℕ) : ModuleCat.{u} R := (cech R F V U).homology n

theorem cech_def : cech R F V U = cechComplex (cechCube R F V U) := rfl

theorem cechH_def (n : ℕ) : cechH R F V U n = (cech R F V U).homology n := rfl

theorem cech_X (p : ℕ) : (cech R F V U).X p = ModuleCat.of R
    (∀ s : {s : Finset ι // s.card = p + 1}, sectionsOn F (V ⊓ ⨅ i ∈ s.1, U i)) := rfl

theorem cech_d (p : ℕ) :
    (cech R F V U).d p (p + 1) = ModuleCat.ofHom (Cube.d (cechCube R F V U) (p + 1)) :=
  cechComplex_d _ p

theorem cech_d_apply (p : ℕ)
    (x : ∀ s : {s : Finset ι // s.card = p + 1}, sectionsOn F (cechOpen V U s.1))
    (t : {s : Finset ι // s.card = p + 1 + 1}) :
    (show ∀ s : {s : Finset ι // s.card = p + 1 + 1}, sectionsOn F (cechOpen V U s.1) from
      ((cech R F V U).d p (p + 1)).hom x) t = ∑ i : t.1, cubeSign t.1 i.1 •
        sectionsOn.res R F (cechOpen_anti V U (Finset.erase_subset i.1 t.1))
          (x (Cube.eraseIdx t i)) := by
  rw [cech_d]
  exact Cube.d_apply (cechCube R F V U) (p + 1) x t

variable {F} in

def cechMap (φ : F ⟶ G) : cech R F V U ⟶ cech R G V U := cechComplexMap (cechCubeMap R V U φ)

variable {F} in

def cechHMap (φ : F ⟶ G) (n : ℕ) : cechH R F V U n ⟶ cechH R G V U n :=
  HomologicalComplex.homologyMap (cechMap R V U φ) n

@[simps]
def cechModulesFunctor : X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj F := cech R F V U
  map := cechMap R V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance cechModulesFunctor_additive : (cechModulesFunctor R V U).Additive where
  map_add := rfl

@[simps]
def cechHFunctor (n : ℕ) : X.Modules ⥤ ModuleCat.{u} R where
  obj F := cechH R F V U n
  map φ := cechHMap R V U φ n
  map_id F := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_id F
  map_comp := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_comp

instance cechHFunctor_additive (n : ℕ) : (cechHFunctor R V U n).Additive where
  map_add := (cechModulesFunctor R V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_add

@[simp]
theorem cechMap_id : cechMap R V U (𝟙 F) = 𝟙 _ := rfl

variable {F} in

@[reassoc]
theorem cechMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    cechMap R V U (φ ≫ ψ) = cechMap R V U φ ≫ cechMap R V U ψ := rfl

@[simp]
theorem cechHMap_id (n : ℕ) : cechHMap R V U (𝟙 F) n = 𝟙 _ := (cechHFunctor R V U n).map_id F

variable {F} in

@[reassoc]
theorem cechHMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) (n : ℕ) :
    cechHMap R V U (φ ≫ ψ) n = cechHMap R V U φ n ≫ cechHMap R V U ψ n :=
  (cechHFunctor R V U n).map_comp φ ψ

variable {F} in

theorem cechHMap_add (φ ψ : F ⟶ G) (n : ℕ) :
    cechHMap R V U (φ + ψ) n = cechHMap R V U φ n + cechHMap R V U ψ n :=
  (cechHFunctor R V U n).map_add

variable {F} in

def cechMapIso (e : F ≅ G) : cech R F V U ≅ cech R G V U := (cechModulesFunctor R V U).mapIso e

variable {F} in

def cechHMapIso (e : F ≅ G) (n : ℕ) : cechH R F V U n ≅ cechH R G V U n :=
  (cechHFunctor R V U n).mapIso e

variable {F} in

theorem cechHMap_cechClass (φ : F ⟶ G) (n : ℕ)
    (x : LinearMap.ker (Cube.d (cechCube R F V U) (n + 1))) :
    (cechHMap R V U φ n).hom (cechClass (cechCube R F V U) n x) =
      cechClass (cechCube R G V U) n ⟨_, Cube.termMap_mem_ker (cechCubeMap R V U φ) x.2⟩ :=
  homologyMap_cechClass (cechCubeMap R V U φ) n x _ rfl

theorem cechHMap_smulHom_apply (r : R) (n : ℕ) (x : cechH R F V U n) :
    (cechHMap R V U (smulHom F (algebraMap R Γ(X, ⊤) r)) n).hom x = r • x := by
  obtain ⟨x, rfl⟩ := cechClass_surjective (cechCube R F V U) n x
  exact (homologyMap_cechClass (cechCubeMap R V U _) n x (r • x) rfl).trans
    (map_smul (cechClass (cechCube R F V U) n) r x)

theorem cechModulesFunctor_shortExact (S : ShortComplex X.Modules)
    (h : ∀ s : Finset ι, s.Nonempty →
      Function.Injective (S.f.app (cechOpen V U s)) ∧
      Function.Exact (S.f.app (cechOpen V U s)) (S.g.app (cechOpen V U s)) ∧
      Function.Surjective (S.g.app (cechOpen V U s))) :
    (S.map (cechModulesFunctor R V U)).ShortExact :=
  cechFunctor_shortExact (S.map (cechCubeFunctor R V U)) fun s hs =>
    ModuleCat.shortComplex_shortExact _ (h s hs).2.1 (h s hs).1 (h s hs).2.2

theorem isZero_cech_X [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    IsZero ((cech R F V U).X n) := isZero_cechComplex_X _ h

theorem isZero_cechH [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    IsZero (cechH R F V U n) := isZero_cechComplex_homology _ h

theorem subsingleton_cechH [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    Subsingleton (cechH R F V U n) := ModuleCat.isZero_iff_subsingleton.1 (isZero_cechH R F V U h)

variable {V U} in

def cechTopIso (h : ∀ i, U i ≤ V) : cech R F ⊤ U ≅ cech R F V U :=
  presheafCechTopIso (sectionsPresheaf R F) h

variable {V U} in

theorem cechTopIso_hom (h : ∀ i, U i ≤ V) : (cechTopIso R F h).hom =
    cechComplexMap (cechCubeRes R F (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)) := rfl

variable {F V U} in

@[reassoc]
theorem cechTopIso_naturality (h : ∀ i, U i ≤ V) (φ : F ⟶ G) :
    cechMap R ⊤ U φ ≫ (cechTopIso R G h).hom = (cechTopIso R F h).hom ≫ cechMap R V U φ :=
  congrArg cechComplexMap (presheafCubeRes_naturality (sectionsPresheafMap R φ)
    (cechOpen_mono (le_top (a := V)) fun _ => le_rfl))

def cechInfIso : cech R F V U ≅ cech R F V fun i => V ⊓ U i :=
  (cechFunctor ι R).mapIso
    (presheafCubeCongr (sectionsPresheaf R F) fun s => (cechOpen_inf_family V U s).symm)

@[simp]
theorem d_cechRestrictions (x : sectionsOn F V) :
    Cube.d (cechCube R F V U) 1 (cechRestrictions R F V U x) = 0 :=
  d_presheafCechAug (sectionsPresheaf R F) V U x

def toCechH : sectionsOn F V →ₗ[R] cechH R F V U 0 := presheafToCechH (sectionsPresheaf R F) V U

theorem toCechH_apply (x : sectionsOn F V) : toCechH R F V U x =
    cechClass (cechCube R F V U) 0 ⟨cechRestrictions R F V U x, d_cechRestrictions R F V U x⟩ :=
  presheafToCechH_apply (sectionsPresheaf R F) V U x

variable {F} in

theorem cechHMap_toCechH (φ : F ⟶ G) (x : sectionsOn F V) :
    (cechHMap R V U φ 0).hom (toCechH R F V U x) = toCechH R G V U (sectionsOn.map R φ V x) :=
  homologyMap_presheafToCechH V U (sectionsPresheafMap R φ) x

variable {V U} (hc : V ≤ ⨆ i, U i)

omit [LinearOrder ι] in
include hc in

theorem cechRestrictions_injective : Function.Injective (cechRestrictions R F V U) :=
  presheafCechAug_injective (T := X.toPresheafedSpace.carrier) (isSheaf_sectionsPresheaf R F) hc

include hc in

theorem cechRestrictions_exact :
    Function.Exact (cechRestrictions R F V U) (Cube.d (cechCube R F V U) 1) :=
  presheafCechAug_exact (T := X.toPresheafedSpace.carrier) (isSheaf_sectionsPresheaf R F) hc

include hc in

theorem cechCube_exactAt_zero_one :
    (cubeComplex (cechCube R F V U)).ExactAt 0 ∧ (cubeComplex (cechCube R F V U)).ExactAt 1 :=
  presheafCube_exactAt_zero_one (T := X.toPresheafedSpace.carrier)
    (isSheaf_sectionsPresheaf R F) hc

include hc in

theorem toCechH_bijective : Function.Bijective (toCechH R F V U) :=
  presheafToCechH_bijective (T := X.toPresheafedSpace.carrier) (isSheaf_sectionsPresheaf R F) hc

def cechHZeroEquiv : cechH R F V U 0 ≃ₗ[R] sectionsOn F V :=
  (LinearEquiv.ofBijective _ (toCechH_bijective R F hc)).symm

@[simp]
theorem cechHZeroEquiv_symm_apply (x : sectionsOn F V) :
    (cechHZeroEquiv R F hc).symm x = toCechH R F V U x := rfl

@[simp]
theorem cechHZeroEquiv_toCechH (x : sectionsOn F V) :
    cechHZeroEquiv R F hc (toCechH R F V U x) = x := (cechHZeroEquiv R F hc).apply_symm_apply x

variable {F} in

theorem cechHZeroEquiv_map (φ : F ⟶ G) (x : cechH R F V U 0) :
    cechHZeroEquiv R G hc ((cechHMap R V U φ 0).hom x) =
      sectionsOn.map R φ V (cechHZeroEquiv R F hc x) := by
  obtain ⟨y, rfl⟩ := (toCechH_bijective R F hc).2 x
  rw [cechHMap_toCechH, cechHZeroEquiv_toCechH, cechHZeroEquiv_toCechH]

def cechHZeroEquivCohOn : cechH R F V U 0 ≃ₗ[R] cohOn F V 0 :=
  (cechHZeroEquiv R F hc).trans (cohOn.zeroEquiv R F V).symm

variable {F} in

theorem cechHZeroEquivCohOn_map (φ : F ⟶ G) (x : cechH R F V U 0) :
    cechHZeroEquivCohOn R G hc ((cechHMap R V U φ 0).hom x) =
      cohOn.map R φ V 0 (cechHZeroEquivCohOn R F hc x) := by
  apply (cohOn.zeroEquiv R G V).injective
  simp only [cechHZeroEquivCohOn, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    cohOn.zeroEquiv_map, cechHZeroEquiv_map]

end Basic

def cechHZeroTopEquiv [LinearOrder ι] (F : X.Modules) {U : ι → X.Opens} (hc : ⨆ i, U i = ⊤) :
    cechH Γ(X, ⊤) F ⊤ U 0 ≃ₗ[Γ(X, ⊤)] Γ(F, ⊤) :=
  (cechHZeroEquiv Γ(X, ⊤) F hc.ge).trans (sectionsOn.topEquiv F)

section Scalars

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  (F : X.Modules) {G : X.Modules} (V : X.Opens) (U : ι → X.Opens)

def cechAbCubeToCube :
    Cube.SemiHom (Int.castRingHom R) (cechAbCube F.presheaf V U) (cechCube R F V U) where
  app s :=
    { toFun := (sectionsOn.toΓ F (cechOpen V U s)).symm
      map_add' := map_add _
      map_smul' := fun n x => (map_zsmul (sectionsOn.toΓ F (cechOpen V U s)).symm n x).trans
        (Int.cast_smul_eq_zsmul R n _).symm }
  app_res _ _ := rfl

def cechCubeIntIso : cechCube ℤ F V U ≅ cechAbCube F.presheaf V U :=
  Cube.isoMk (fun s => (sectionsOn.toΓ F (cechOpen V U s)).toIntLinearEquiv) fun _ _ => rfl

variable (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S] [IsScalarTower R S Γ(X, ⊤)]

def cechCubeScalars : Cube.SemiHom (algebraMap R S) (cechCube R F V U) (cechCube S F V U) where
  app s :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun r (x : sectionsOn F (cechOpen V U s)) => (algebraMap_smul S r x).symm }
  app_res _ _ := rfl

def cechCubeRestrictScalarsIso :
    cechCube R F V U ≅ cechCube S F V U ⋙ ModuleCat.restrictScalars (algebraMap R S) :=
  Cube.isoMk (fun s =>
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r (x : sectionsOn F (cechOpen V U s)) => (algebraMap_smul S r x).symm })
    fun _ _ => rfl

variable [LinearOrder ι]

def cechRestrictIso : cech R F V U ≅
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj (cech S F V U) :=
  (cechFunctor ι R).mapIso (cechCubeRestrictScalarsIso R F V U S) ≪≫
    (cechRestrictScalarsIso (algebraMap R S) (cechCube S F V U)).symm

def cechHScalarsEquiv (n : ℕ) : cechH R F V U n ≃+ cechH S F V U n :=
  AddEquiv.ofBijective ((cechCubeScalars R F V U S).homology n).toAddMonoidHom
    ((cechCubeScalars R F V U S).homology_bijective (fun _ _ => Function.bijective_id) n)

theorem cechHScalarsEquiv_apply (n : ℕ) (x : cechH R F V U n) :
    cechHScalarsEquiv R F V U S n x = (cechCubeScalars R F V U S).homology n x := rfl

theorem cechHScalarsEquiv_smul (n : ℕ) (r : R) (x : cechH R F V U n) :
    cechHScalarsEquiv R F V U S n (r • x) = algebraMap R S r • cechHScalarsEquiv R F V U S n x :=
  map_smulₛₗ ((cechCubeScalars R F V U S).homology n) r x

variable {F} in

theorem cechHScalarsEquiv_map (φ : F ⟶ G) (n : ℕ) (x : cechH R F V U n) :
    cechHScalarsEquiv R G V U S n ((cechHMap R V U φ n).hom x) =
      (cechHMap S V U φ n).hom (cechHScalarsEquiv R F V U S n x) :=
  (cechCubeScalars R F V U S).homology_naturality (cechCubeScalars R G V U S)
    (cechCubeMap R V U φ) (cechCubeMap S V U φ) (fun _ _ _ => rfl) n x

def cechAbHEquiv (n : ℕ) : cechAbH F.presheaf V U n ≃+ cechH R F V U n :=
  AddEquiv.ofBijective ((cechAbCubeToCube R F V U).homology n).toAddMonoidHom
    ((cechAbCubeToCube R F V U).homology_bijective (fun _ _ => Function.bijective_id) n)

theorem cechAbHEquiv_apply (n : ℕ) (x : cechAbH F.presheaf V U n) :
    cechAbHEquiv R F V U n x = (cechAbCubeToCube R F V U).homology n x := rfl

variable {F} in

theorem cechAbHEquiv_map (φ : F ⟶ G) (n : ℕ) (x : cechAbH F.presheaf V U n) :
    cechAbHEquiv R G V U n ((cechAbHMap V U φ.mapPresheaf n).hom x) =
      (cechHMap R V U φ n).hom (cechAbHEquiv R F V U n x) :=
  (cechAbCubeToCube R F V U).homology_naturality (cechAbCubeToCube R G V U)
    (cechAbCubeMap V U φ.mapPresheaf) (cechCubeMap R V U φ) (fun _ _ _ => rfl) n x

theorem smul_cechAbHEquiv (r : R) (n : ℕ) (x : cechAbH F.presheaf V U n) :
    r • cechAbHEquiv R F V U n x = cechAbHEquiv R F V U n
      ((cechAbHMap V U (smulHom F (algebraMap R Γ(X, ⊤) r)).mapPresheaf n).hom x) := by
  rw [cechAbHEquiv_map, cechHMap_smulHom_apply]

theorem cechAbHEquiv_toCechAbH (x : sectionsOn F V) :
    cechAbHEquiv R F V U 0 (toCechAbH F.presheaf V U (sectionsOn.toΓ F V x)) =
      toCechH R F V U x :=
  (cechAbCubeToCube R F V U).homology_cechAugHomology _

end Scalars

section Morphism

variable (g : Y ⟶ X) (V : X.Opens) (U : ι → X.Opens)

theorem preimage_cechOpen (s : Finset ι) :
    g ⁻¹ᵁ cechOpen V U s = cechOpen (g ⁻¹ᵁ V) (fun i => g ⁻¹ᵁ U i) s := by
  ext x
  exact mem_cechOpen.trans (mem_cechOpen (V := g ⁻¹ᵁ V) (U := fun i => g ⁻¹ᵁ U i)).symm

variable {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)] {S : Type t} [CommRing S]
  [Algebra S Γ(Y, ⊤)] {σ : R →+* S}
  {g} (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
  {F : X.Modules} {G : Y.Modules} (φ : F ⟶ (Scheme.Modules.pushforward g).obj G)

def sectionsOn.mapOver (W : X.Opens) : sectionsOn F W →ₛₗ[σ] sectionsOn G (g ⁻¹ᵁ W) where
  toFun x := (sectionsOn.toΓ G (g ⁻¹ᵁ W)).symm (φ.app W (sectionsOn.toΓ F W x))
  map_add' x y := map_add (φ.app W).hom x y
  map_smul' r x := by
    have h : g.app W (restrictGlobal X W (algebraMap R Γ(X, ⊤) r)) =
        restrictGlobal Y (g ⁻¹ᵁ W) (algebraMap S Γ(Y, ⊤) (σ r)) := by
      rw [← hσ]
      exact ConcreteCategory.congr_hom (g.naturality (homOfLE le_top : W ⟶ ⊤).op) _
    refine (φ.app_smul (restrictGlobal X W (algebraMap R Γ(X, ⊤) r)) x).trans ?_
    exact congrArg (fun a : Γ(Y, g ⁻¹ᵁ W) =>
      (a • (show Γ(G, g ⁻¹ᵁ W) from φ.app W (sectionsOn.toΓ F W x)) : Γ(G, g ⁻¹ᵁ W))) h

theorem sectionsOn.toΓ_mapOver (W : X.Opens) (x : sectionsOn F W) :
    sectionsOn.toΓ G (g ⁻¹ᵁ W) (sectionsOn.mapOver hσ φ W x) = φ.app W (sectionsOn.toΓ F W x) :=
  rfl

theorem sectionsOn.mapOver_res {W W' : X.Opens} (h : W' ≤ W) (x : sectionsOn F W) :
    sectionsOn.mapOver hσ φ W' (sectionsOn.res R F h x) =
      sectionsOn.res S G (g.preimage_mono h) (sectionsOn.mapOver hσ φ W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

def cechCubeMapOver :
    Cube.SemiHom σ (cechCube R F V U) (cechCube S G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i) where
  app s := (sectionsOn.res S G (preimage_cechOpen g V U s).ge).comp
    (sectionsOn.mapOver hσ φ (cechOpen V U s))
  app_res {s t} h x :=
    (congrArg (sectionsOn.res S G (preimage_cechOpen g V U t).ge)
      (sectionsOn.mapOver_res hσ φ (cechOpen_anti V U h) x)).trans
      ((sectionsOn.res_res S G _ _ _).trans
        (sectionsOn.res_res S G _ (cechOpen_anti _ _ h) _).symm)

theorem cechCubeMapOver_app (s : Finset ι) (x : sectionsOn F (cechOpen V U s)) :
    (cechCubeMapOver V U hσ φ).app s x = sectionsOn.res S G (preimage_cechOpen g V U s).ge
      (sectionsOn.mapOver hσ φ (cechOpen V U s) x) := rfl

theorem cechCubeMapOver_id_bijective (s : Finset ι) : Function.Bijective
    ((cechCubeMapOver V U hσ (𝟙 ((Scheme.Modules.pushforward g).obj G))).app s) :=
  (sectionsOn.congrOpens S G (preimage_cechOpen g V U s)).bijective

variable [Algebra R Γ(Y, ⊤)]
  (hg : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r)

variable (G) in

def cechCubePushforwardIso : cechCube R ((Scheme.Modules.pushforward g).obj G) V U ≅
    cechCube R G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i :=
  Cube.isoMk (fun s => LinearEquiv.ofBijective _
    (cechCubeMapOver_id_bijective (σ := RingHom.id R) V U hg s))
    (cechCubeMapOver (σ := RingHom.id R) V U hg (𝟙 _)).app_res

theorem cechCubePushforwardIso_hom_app_apply (s : Finset ι)
    (x : sectionsOn G (g ⁻¹ᵁ cechOpen V U s)) :
    ((cechCubePushforwardIso V U G hg).hom.app s).hom x =
      sectionsOn.res R G (preimage_cechOpen g V U s).ge x := rfl

@[reassoc]
theorem cechCubePushforwardIso_naturality {G' : Y.Modules} (ψ : G ⟶ G') :
    cechCubeMap R V U ((Scheme.Modules.pushforward g).map ψ) ≫
        (cechCubePushforwardIso V U G' hg).hom =
      (cechCubePushforwardIso V U G hg).hom ≫ cechCubeMap R _ _ ψ :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext fun x =>
    sectionsOn.res_map R ψ (preimage_cechOpen g V U s).ge x))

variable (G) in

def cechPushforwardIso [LinearOrder ι] : cech R ((Scheme.Modules.pushforward g).obj G) V U ≅
    cech R G (g ⁻¹ᵁ V) fun i => g ⁻¹ᵁ U i :=
  (cechFunctor ι R).mapIso (cechCubePushforwardIso V U G hg)

end Morphism

section Two

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (F : X.Modules) (V : X.Opens)
  (U : Fin 2 → X.Opens)

def cechTwoXZero :
    (cech R F V U).X 0 ≃ₗ[R] sectionsOn F (V ⊓ U 0) × sectionsOn F (V ⊓ U 1) :=
  Cube.termOneFinTwo (cechCube R F V U) ≪≫ₗ
    (sectionsOn.congrOpens R F (cechOpen_singleton V U 0)).prodCongr
      (sectionsOn.congrOpens R F (cechOpen_singleton V U 1))

def cechTwoXOne : (cech R F V U).X 1 ≃ₗ[R] sectionsOn F (V ⊓ (U 0 ⊓ U 1)) :=
  Cube.termTwoFinTwo (cechCube R F V U) ≪≫ₗ sectionsOn.congrOpens R F (cechOpen_pair V U 0 1)

theorem cechTwo_d (x : (cech R F V U).X 0) :
    cechTwoXOne R F V U (((cech R F V U).d 0 1).hom x) =
      sectionsOn.res R F (inf_le_inf_left V inf_le_right) (cechTwoXZero R F V U x).2 -
        sectionsOn.res R F (inf_le_inf_left V inf_le_left) (cechTwoXZero R F V U x).1 := by
  rw [cech_d R F V U 0]
  refine (congrArg (sectionsOn.congrOpens R F (cechOpen_pair V U 0 1))
    (Cube.d_one_finTwo (cechCube R F V U) x)).trans ((map_sub _ _ _).trans ?_)
  exact congrArg₂ (· - ·)
    ((sectionsOn.res_res R F _ _ _).trans
      (sectionsOn.res_res R F (cechOpen_singleton V U 1).ge _ _).symm)
    ((sectionsOn.res_res R F _ _ _).trans
      (sectionsOn.res_res R F (cechOpen_singleton V U 0).ge _ _).symm)

theorem cechTwoXZero_cechRestrictions (x : sectionsOn F V) :
    cechTwoXZero R F V U (cechRestrictions R F V U x) =
      (sectionsOn.res R F inf_le_left x, sectionsOn.res R F inf_le_left x) :=
  Prod.ext (sectionsOn.res_res R F _ (cechOpen_singleton V U 0).ge x)
    (sectionsOn.res_res R F _ (cechOpen_singleton V U 1).ge x)

theorem isZero_cechTwo_X {n : ℕ} (h : 2 ≤ n) : IsZero ((cech R F V U).X n) :=
  isZero_cech_X R F V U (by rwa [Fintype.card_fin])

theorem isZero_cechH_one_iff_surjective :
    IsZero (cechH R F V U 1) ↔ Function.Surjective ((cech R F V U).d 0 1).hom := by
  haveI := Cube.subsingleton_term (cechCube R F V U) (p := 0 + 2 + 1) (by simp)
  rw [cech_d R F V U 0]
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ _).symm.trans
    ((cechComplex_exactAt_succ_iff (cechCube R F V U) 0).trans (forall_congr' fun x => ?_))
  exact ⟨fun h => h.1 (Subsingleton.elim _ _), fun h => ⟨fun _ => h, fun _ => Subsingleton.elim _ _⟩⟩

end Two

section Affine

variable {A : CommRingCat.{u}} (M : ModuleCat.{u} A)

def tildeToSections (W : (Spec A).Opens) : M →ₗ[A] sectionsOn (tilde M) W :=
  (sectionsOn.specEquiv (tilde M) W).symm.toLinearMap ∘ₗ (tilde.toOpen M W).hom

@[simp]
theorem res_tildeToSections {W W' : (Spec A).Opens} (h : W' ≤ W) (m : M) :
    sectionsOn.res A (tilde M) h (tildeToSections M W m) = tildeToSections M W' m := rfl

def basicOpenFamily (f : ι → A) : ι → (Spec A).Opens := fun i => PrimeSpectrum.basicOpen (f i)

theorem basicOpenFamily_apply (f : ι → A) (i : ι) :
    basicOpenFamily f i = PrimeSpectrum.basicOpen (f i) := rfl

theorem isLocalizedModule_tildeToSections (f : A) {W : (Spec A).Opens}
    (h : W = PrimeSpectrum.basicOpen f) : IsLocalizedModule.Away f (tildeToSections M W) := by
  have h₀ : IsLocalizedModule.Away f (tilde.toOpen M W).hom := by
    subst h
    infer_instance
  exact IsLocalizedModule.of_linearEquiv (.powers f)
    (tilde.toOpen M W).hom (sectionsOn.specEquiv (tilde M) W).symm

theorem cechOpen_basicOpenFamily (f : ι → A) (s : Finset ι) :
    cechOpen ⊤ (basicOpenFamily f) s = PrimeSpectrum.basicOpen (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [cechOpen_empty, Finset.prod_empty]
    exact PrimeSpectrum.basicOpen_one.symm
  | insert a s ha ih =>
    rw [cechOpen_insert, ih, Finset.prod_insert ha]
    exact (PrimeSpectrum.basicOpen_mul _ _).symm

theorem iSup_basicOpenFamily_eq_top_iff (f : ι → A) :
    ⨆ i, basicOpenFamily f i = ⊤ ↔ Ideal.span (Set.range f) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff

def locCubeIsoCechCube (f : ι → A) : locCube f M ≅ cechCube A (tilde M) ⊤ (basicOpenFamily f) :=
  locCubeIso f M _ (fun s => tildeToSections M (cechOpen ⊤ (basicOpenFamily f) s))
    (hg := fun s => isLocalizedModule_tildeToSections M _ (cechOpen_basicOpenFamily f s))
    fun h m => res_tildeToSections M (cechOpen_anti _ _ h) m

theorem cechCube_tilde_exactAt [LinearOrder ι] [Finite ι] {f : ι → A}
    (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) :
    (cubeComplex (cechCube A (tilde M) ⊤ (basicOpenFamily f))).ExactAt p :=
  cubeComplex_exactAt_of_isLocalizedModule _ f
    (fun s => tildeToSections M (cechOpen ⊤ (basicOpenFamily f) s))
    (fun s => isLocalizedModule_tildeToSections M _ (cechOpen_basicOpenFamily f s))
    (fun h m => res_tildeToSections M (cechOpen_anti _ _ h) m) hf p

theorem isZero_cechH_tilde_succ [LinearOrder ι] [Finite ι] {f : ι → A}
    (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) :
    IsZero (cechH A (tilde M) ⊤ (basicOpenFamily f) (p + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((cechComplex_exactAt_succ_iff_cube _ p).2 (cechCube_tilde_exactAt M hf (p + 2)))

def cechHZeroTildeEquiv [LinearOrder ι] {f : ι → A} (hf : Ideal.span (Set.range f) = ⊤) :
    cechH A (tilde M) ⊤ (basicOpenFamily f) 0 ≃ₗ[A] M :=
  cechHZeroEquiv A (tilde M) ((iSup_basicOpenFamily_eq_top_iff f).2 hf).ge ≪≫ₗ
    sectionsOn.specEquiv (tilde M) ⊤ ≪≫ₗ (tilde.isoTop M).toLinearEquiv.symm

theorem cechHZeroTildeEquiv_symm_apply [LinearOrder ι] {f : ι → A}
    (hf : Ideal.span (Set.range f) = ⊤) (m : M) :
    (cechHZeroTildeEquiv M hf).symm m =
      toCechH A (tilde M) ⊤ (basicOpenFamily f) (tildeToSections M ⊤ m) := rfl

def awayTransition {a b : A} (h : a ∣ b) :
    LocalizedModule (.powers a) M →ₗ[A] LocalizedModule (.powers b) M :=
  LocalizedModule.lift _ (LocalizedModule.mkLinearMap _ M)
    (isUnit_powers_of_dvd h (LocalizedModule.mkLinearMap _ M))

@[simp]
theorem awayTransition_mk_one {a b : A} (h : a ∣ b) (m : M) :
    awayTransition M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 :=
  LocalizedModule.lift_mk_one _ _ _ m

def sectionsAwayEquiv (f : A) {W : (Spec A).Opens} (h : W = PrimeSpectrum.basicOpen f) :
    sectionsOn (tilde M) W ≃ₗ[A] LocalizedModule (.powers f) M :=
  haveI := isLocalizedModule_tildeToSections M f h
  IsLocalizedModule.linearEquiv (.powers f) (tildeToSections M W) (LocalizedModule.mkLinearMap _ M)

@[simp]
theorem sectionsAwayEquiv_tildeToSections (f : A) {W : (Spec A).Opens}
    (h : W = PrimeSpectrum.basicOpen f) (m : M) :
    sectionsAwayEquiv M f h (tildeToSections M W m) = LocalizedModule.mk m 1 :=
  haveI := isLocalizedModule_tildeToSections M f h
  IsLocalizedModule.linearEquiv_apply (.powers f) _ _ m

theorem sectionsAwayEquiv_res {a b : A} (hab : a ∣ b) {W W' : (Spec A).Opens}
    (h : W = PrimeSpectrum.basicOpen a) (h' : W' = PrimeSpectrum.basicOpen b) (hW : W' ≤ W)
    (x : sectionsOn (tilde M) W) :
    sectionsAwayEquiv M b h' (sectionsOn.res A (tilde M) hW x) =
      awayTransition M hab (sectionsAwayEquiv M a h x) := by
  haveI := isLocalizedModule_tildeToSections M a h
  have := IsLocalizedModule.ext (.powers a) (tildeToSections M W)
    (isUnit_powers_of_dvd hab (LocalizedModule.mkLinearMap _ M))
    (j := (sectionsAwayEquiv M b h').toLinearMap ∘ₗ sectionsOn.res A (tilde M) hW)
    (k := awayTransition M hab ∘ₗ (sectionsAwayEquiv M a h).toLinearMap) (by ext m; simp)
  exact congr($this x)

variable (f g : A)

abbrev twoCharts : Fin 2 → (Spec A).Opens := basicOpenFamily ![f, g]

theorem twoCharts_zero : twoCharts f g 0 = PrimeSpectrum.basicOpen f := rfl

theorem twoCharts_one : twoCharts f g 1 = PrimeSpectrum.basicOpen g := rfl

theorem twoCharts_inf : ⊤ ⊓ (twoCharts f g 0 ⊓ twoCharts f g 1) = PrimeSpectrum.basicOpen (f * g) :=
  (top_inf_eq _).trans (PrimeSpectrum.basicOpen_mul f g).symm

def twoChartsXZero : (cech A (tilde M) ⊤ (twoCharts f g)).X 0 ≃ₗ[A]
    LocalizedModule (.powers f) M × LocalizedModule (.powers g) M :=
  cechTwoXZero A (tilde M) ⊤ (twoCharts f g) ≪≫ₗ
    (sectionsAwayEquiv M f (top_inf_eq _)).prodCongr (sectionsAwayEquiv M g (top_inf_eq _))

def twoChartsXOne :
    (cech A (tilde M) ⊤ (twoCharts f g)).X 1 ≃ₗ[A] LocalizedModule (.powers (f * g)) M :=
  cechTwoXOne A (tilde M) ⊤ (twoCharts f g) ≪≫ₗ sectionsAwayEquiv M (f * g) (twoCharts_inf f g)

theorem twoCharts_d (x : (cech A (tilde M) ⊤ (twoCharts f g)).X 0) :
    twoChartsXOne M f g (((cech A (tilde M) ⊤ (twoCharts f g)).d 0 1).hom x) =
      awayTransition M (dvd_mul_left g f) (twoChartsXZero M f g x).2 -
        awayTransition M (dvd_mul_right f g) (twoChartsXZero M f g x).1 :=
  (congrArg (sectionsAwayEquiv M (f * g) (twoCharts_inf f g))
    (cechTwo_d A (tilde M) ⊤ (twoCharts f g) x)).trans ((map_sub _ _ _).trans (congrArg₂ (· - ·)
      (sectionsAwayEquiv_res M _ (top_inf_eq _) _ _ _)
      (sectionsAwayEquiv_res M _ (top_inf_eq _) _ _ _)))

theorem twoChartsXZero_cechRestrictions (m : M) :
    twoChartsXZero M f g (cechRestrictions A (tilde M) ⊤ (twoCharts f g) (tildeToSections M ⊤ m)) =
      (LocalizedModule.mk m 1, LocalizedModule.mk m 1) :=
  Prod.ext (sectionsAwayEquiv_tildeToSections M f (top_inf_eq _) m)
    (sectionsAwayEquiv_tildeToSections M g (top_inf_eq _) m)

theorem isZero_cechH_twoCharts_one_iff : IsZero (cechH A (tilde M) ⊤ (twoCharts f g) 1) ↔
    ∀ z, ∃ a b, awayTransition M (dvd_mul_left g f) b - awayTransition M (dvd_mul_right f g) a =
      z := by
  rw [isZero_cechH_one_iff_surjective]
  constructor
  · intro h z
    obtain ⟨x, hx⟩ := h ((twoChartsXOne M f g).symm z)
    exact ⟨_, _, by rw [← twoCharts_d, hx, LinearEquiv.apply_symm_apply]⟩
  · intro h z
    obtain ⟨a, b, hab⟩ := h (twoChartsXOne M f g z)
    refine ⟨(twoChartsXZero M f g).symm (a, b), (twoChartsXOne M f g).injective ?_⟩
    rw [twoCharts_d, LinearEquiv.apply_symm_apply, hab]

theorem span_range_pair_one_sub : Ideal.span (Set.range ![f, 1 - f]) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (by
    simpa using Ideal.add_mem _ (Ideal.subset_span (s := Set.range ![f, 1 - f]) ⟨0, rfl⟩)
      (Ideal.subset_span ⟨1, rfl⟩))

theorem iSup_twoCharts_one_sub : ⨆ i, twoCharts f (1 - f) i = ⊤ :=
  (iSup_basicOpenFamily_eq_top_iff _).2 (span_range_pair_one_sub f)

def cechHZeroTwoChartsEquiv : cechH A (tilde M) ⊤ (twoCharts f (1 - f)) 0 ≃ₗ[A] M :=
  cechHZeroTildeEquiv M (span_range_pair_one_sub f)

theorem isZero_cechH_twoCharts_succ (p : ℕ) :
    IsZero (cechH A (tilde M) ⊤ (twoCharts f (1 - f)) (p + 1)) :=
  isZero_cechH_tilde_succ M (span_range_pair_one_sub f) p

def cechStructureIso [LinearOrder ι] (V : (Spec A).Opens) (U : ι → (Spec A).Opens) :
    cech A (tilde (ModuleCat.of A A)) V U ≅ cech A (structureModule (Spec A)) V U :=
  cechMapIso A V U tildeSelf

def cechHZeroStructureTwoChartsEquiv :
    cechH A (structureModule (Spec A)) ⊤ (twoCharts f (1 - f)) 0 ≃ₗ[A] A :=
  (cechHMapIso A ⊤ (twoCharts f (1 - f)) tildeSelf 0).toLinearEquiv.symm ≪≫ₗ
    cechHZeroTwoChartsEquiv (ModuleCat.of A A) f

theorem isZero_cechH_structure_twoCharts_succ (p : ℕ) :
    IsZero (cechH A (structureModule (Spec A)) ⊤ (twoCharts f (1 - f)) (p + 1)) :=
  (isZero_cechH_twoCharts_succ (ModuleCat.of A A) f p).of_iso
    (cechHMapIso A ⊤ (twoCharts f (1 - f)) tildeSelf (p + 1)).symm

theorem exists_pow_mul_pow_eq_of_isZero_cechH
    (h : IsZero (cechH A (structureModule (Spec A)) ⊤ (twoCharts f g) 1)) :
    ∃ (n k : ℕ) (a b : A), f ^ n * g ^ k = f ^ (n + 1) * b + g ^ (k + 1) * a := by
  obtain ⟨a, b, hab⟩ := (isZero_cechH_twoCharts_one_iff (ModuleCat.of A A) f g).1
    (h.of_iso (cechHMapIso A ⊤ (twoCharts f g) tildeSelf 1))
    (LocalizedModule.mk (1 : A) ⟨f * g, 1, pow_one _⟩)
  obtain ⟨n, a', ha⟩ := IsLocalizedModule.Away.surj (LocalizedModule.mkLinearMap _ _) f a
  obtain ⟨k, b', hb⟩ := IsLocalizedModule.Away.surj (LocalizedModule.mkLinearMap _ _) g b
  let l : A →ₗ[A] LocalizedModule (.powers (f * g)) A := LocalizedModule.mkLinearMap _ _
  have h₁ : f ^ n • awayTransition (ModuleCat.of A A) (dvd_mul_right f g) a = l a' := by
    rw [← map_smul, ha]; exact awayTransition_mk_one (ModuleCat.of A A) _ a'
  have h₂ : g ^ k • awayTransition (ModuleCat.of A A) (dvd_mul_left g f) b = l b' := by
    rw [← map_smul, hb]; exact awayTransition_mk_one (ModuleCat.of A A) _ b'
  have h₃ : (f * g) • LocalizedModule.mk (1 : A) (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g)) =
      l 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g)) (1 : A)
  have h₄ : l ((f ^ n * g ^ k) • (1 : A)) =
      l ((f ^ n * (f * g)) • b' - (g ^ k * (f * g)) • a') := by
    rw [map_sub, map_smul, map_smul, map_smul, ← h₁, ← h₂, ← h₃, ← hab]
    simp only [smul_sub, smul_smul]
    congr 2 <;> ring
  obtain ⟨m, hm⟩ := IsLocalizedModule.Away.exists_of_eq (f * g) h₄
  refine ⟨n + m, k + m, -(f ^ (m + 1) * a'), g ^ (m + 1) * b', ?_⟩
  simp only [smul_eq_mul, mul_pow] at hm
  linear_combination hm

end Affine

example :
    letI := algebraΓSpec (.of ℤ)
    Nontrivial (cechH (CommRingCat.of ℤ) (structureModule (Spec (.of ℤ))) ⊤
      (twoCharts (A := .of ℤ) 3 (1 - 3)) 0) ∧
    IsZero (cechH (CommRingCat.of ℤ) (structureModule (Spec (.of ℤ))) ⊤
      (twoCharts (A := .of ℤ) 3 (1 - 3)) 1) :=
  ⟨(cechHZeroStructureTwoChartsEquiv (A := .of ℤ) 3).toEquiv.nontrivial,
    isZero_cechH_structure_twoCharts_succ (A := .of ℤ) 3 0⟩

example : Nontrivial (cechAbH (structureModule (Spec (.of ℤ))).presheaf ⊤
    (twoCharts (A := .of ℤ) 3 (1 - 3)) 0) :=
  letI := algebraΓSpec (.of ℤ)
  haveI := (cechHZeroStructureTwoChartsEquiv (A := .of ℤ) 3).toEquiv.nontrivial
  (cechAbHEquiv (CommRingCat.of ℤ) (structureModule (Spec (.of ℤ))) ⊤
    (twoCharts (A := .of ℤ) 3 (1 - 3)) 0).toEquiv.nontrivial

example {A : CommRingCat.{u}} (M : ModuleCat.{u} A) (f g : A) (m : M) :
    twoChartsXOne M f g (((cech A (tilde M) ⊤ (twoCharts f g)).d 0 1).hom
      ((twoChartsXZero M f g).symm (LocalizedModule.mk m 1, 0))) = -LocalizedModule.mk m 1 := by
  rw [twoCharts_d, LinearEquiv.apply_symm_apply, map_zero, awayTransition_mk_one, zero_sub]

example :
    letI := algebraΓSpec (.of (Polynomial ℤ))
    ¬ IsZero (cechH (CommRingCat.of (Polynomial ℤ)) (structureModule (Spec (.of (Polynomial ℤ)))) ⊤
      (twoCharts (A := .of (Polynomial ℤ)) (Polynomial.C 2) Polynomial.X) 1) := by
  intro h
  obtain ⟨n, k, a, b, hab⟩ := exists_pow_mul_pow_eq_of_isZero_cechH (A := .of (Polynomial ℤ))
    (Polynomial.C 2) Polynomial.X h
  have h₁ : (Polynomial.C (2 : ℤ) ^ n * Polynomial.X ^ k).coeff k =
      (Polynomial.C (2 : ℤ) ^ (n + 1) * b + Polynomial.X ^ (k + 1) * a).coeff k :=
    congrArg (fun p : Polynomial ℤ => p.coeff k) hab
  rw [← map_pow, ← map_pow, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_self, Polynomial.coeff_X_pow_mul', if_neg (by omega), add_zero,
    pow_succ, mul_assoc] at h₁
  have h₂ := mul_left_cancel₀ (by positivity : (2 : ℤ) ^ n ≠ 0) h₁
  omega

end GlobalTheory
