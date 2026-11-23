import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HomologyRestrictScalarsBijective

open CategoryTheory Limits TopologicalSpace Opposite

universe w v u

noncomputable section

namespace GlobalTheory

section Opens

variable {T : Type w} [TopologicalSpace T] {ι κ : Type}

def cechOpen (V : Opens T) (U : ι → Opens T) (s : Finset ι) : Opens T := V ⊓ ⨅ i ∈ s, U i

variable (V : Opens T) (U : ι → Opens T)

theorem cechOpen_def (s : Finset ι) : cechOpen V U s = V ⊓ ⨅ i ∈ s, U i := rfl

theorem cechOpen_eq_inf (s : Finset ι) : cechOpen V U s = V ⊓ s.inf U := by
  rw [cechOpen, Finset.inf_eq_iInf]

variable {V U} in

theorem le_cechOpen_iff {W : Opens T} {s : Finset ι} :
    W ≤ cechOpen V U s ↔ W ≤ V ∧ ∀ i ∈ s, W ≤ U i := by
  simp [cechOpen]

variable {V U} in

theorem mem_cechOpen {x : T} {s : Finset ι} :
    x ∈ cechOpen V U s ↔ x ∈ V ∧ ∀ i ∈ s, x ∈ U i := by
  classical
  rw [cechOpen_eq_inf, Opens.mem_inf]
  refine and_congr Iff.rfl ?_
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih => simp [ih]

theorem cechOpen_le (s : Finset ι) : cechOpen V U s ≤ V := inf_le_left

theorem cechOpen_le_of_mem {s : Finset ι} {i : ι} (h : i ∈ s) : cechOpen V U s ≤ U i :=
  (le_cechOpen_iff.1 le_rfl).2 i h

theorem cechOpen_anti {s t : Finset ι} (h : s ⊆ t) : cechOpen V U t ≤ cechOpen V U s :=
  le_cechOpen_iff.2 ⟨cechOpen_le V U t, fun _ hi => cechOpen_le_of_mem V U (h hi)⟩

@[simp]
theorem cechOpen_empty : cechOpen V U ∅ = V := by simp [cechOpen]

@[simp]
theorem cechOpen_singleton (i : ι) : cechOpen V U {i} = V ⊓ U i := by simp [cechOpen]

theorem cechOpen_insert [DecidableEq ι] (i : ι) (s : Finset ι) :
    cechOpen V U (insert i s) = U i ⊓ cechOpen V U s := by
  rw [cechOpen, cechOpen, Finset.iInf_insert, inf_left_comm]

theorem cechOpen_pair [DecidableEq ι] (i j : ι) : cechOpen V U {i, j} = V ⊓ (U i ⊓ U j) := by
  rw [cechOpen_insert, cechOpen_singleton, inf_left_comm]

theorem cechOpen_union [DecidableEq ι] (s t : Finset ι) :
    cechOpen V U (s ∪ t) = cechOpen V U s ⊓ cechOpen V U t := by
  ext x
  simp only [SetLike.mem_coe, mem_cechOpen, Opens.mem_inf, Finset.mem_union, or_imp, forall_and]
  tauto

theorem cechOpen_top (s : Finset ι) : cechOpen ⊤ U s = ⨅ i ∈ s, U i := top_inf_eq _

variable {V U} in

theorem cechOpen_of_nonempty (h : ∀ i, U i ≤ V) {s : Finset ι} (hs : s.Nonempty) :
    cechOpen V U s = ⨅ i ∈ s, U i := by
  obtain ⟨i, hi⟩ := hs
  exact inf_eq_right.2 ((biInf_le U hi).trans (h i))

variable {V U} in

theorem cechOpen_mono {V' : Opens T} {U' : ι → Opens T} (hV : V' ≤ V) (hU : ∀ i, U' i ≤ U i)
    (s : Finset ι) : cechOpen V' U' s ≤ cechOpen V U s :=
  le_cechOpen_iff.2 ⟨(cechOpen_le _ _ s).trans hV,
    fun i hi => (cechOpen_le_of_mem _ _ hi).trans (hU i)⟩

theorem cechOpen_inf_family (s : Finset ι) :
    cechOpen V (fun i => V ⊓ U i) s = cechOpen V U s := by
  ext x
  simp only [SetLike.mem_coe, mem_cechOpen, Opens.mem_inf]
  exact and_congr_right fun h => by simp [h]

theorem cechOpen_inf_left (W : Opens T) (s : Finset ι) :
    cechOpen (W ⊓ V) U s = W ⊓ cechOpen V U s := inf_assoc _ _ _

theorem cechOpen_map (e : κ ↪ ι) (s : Finset κ) :
    cechOpen V U (s.map e) = cechOpen V (fun k => U (e k)) s := by
  ext x
  simp [mem_cechOpen]

theorem cechOpen_insert_map [DecidableEq ι] (e : κ ↪ ι) (i : ι) (s : Finset κ) :
    cechOpen V U (insert i (s.map e)) = cechOpen (V ⊓ U i) (fun k => U (e k)) s := by
  rw [cechOpen_insert, cechOpen_map, inf_comm V, cechOpen_inf_left]

variable {V U} in

theorem cechOpen_empty_le_iSup (h : V ≤ ⨆ i, U i) :
    cechOpen V U ∅ ≤ ⨆ i, cechOpen V U {i} := by
  simp only [cechOpen_empty, cechOpen_singleton, ← inf_iSup_eq]
  exact le_inf le_rfl h

@[simps obj]
def cechOpenFunctor : Finset ι ⥤ (Opens T)ᵒᵖ where
  obj s := op (cechOpen V U s)
  map f := (homOfLE (cechOpen_anti V U (leOfHom f))).op

end Opens

section Presheaf

variable {T : Type w} [TopologicalSpace T] {ι κ : Type} {R : Type u} [Ring R]

def presheafRes (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{v} R) {W W' : Opens T} (h : W' ≤ W) :
    P.obj (op W) →ₗ[R] P.obj (op W') :=
  (P.map (homOfLE h).op).hom

variable (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{v} R) {Q Q' : (Opens T)ᵒᵖ ⥤ ModuleCat.{v} R}

@[simp]
theorem presheafRes_self {W : Opens T} (h : W ≤ W) (x : P.obj (op W)) : presheafRes P h x = x := by
  have : (homOfLE h).op = 𝟙 (op W) := rfl
  simp [presheafRes, this]

@[simp]
theorem presheafRes_presheafRes {W W' W'' : Opens T} (h : W' ≤ W) (h' : W'' ≤ W')
    (x : P.obj (op W)) : presheafRes P h' (presheafRes P h x) = presheafRes P (h'.trans h) x := by
  have : (homOfLE (h'.trans h)).op = (homOfLE h).op ≫ (homOfLE h').op := rfl
  simp only [presheafRes, this, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem presheafRes_bijective {W W' : Opens T} (h : W' ≤ W) (h' : W ≤ W') :
    Function.Bijective (presheafRes P h) :=
  Function.bijective_iff_has_inverse.2 ⟨presheafRes P h', fun x => by simp, fun x => by simp⟩

def presheafCongr {W W' : Opens T} (h : W = W') : P.obj (op W) ≃ₗ[R] P.obj (op W') :=
  { presheafRes P h.ge with
    invFun := presheafRes P h.le
    left_inv := fun x => by simp
    right_inv := fun x => by simp }

@[simp]
theorem presheafCongr_apply {W W' : Opens T} (h : W = W') (x : P.obj (op W)) :
    presheafCongr P h x = presheafRes P h.ge x := rfl

@[simp]
theorem presheafCongr_symm_apply {W W' : Opens T} (h : W = W') (x : P.obj (op W')) :
    (presheafCongr P h).symm x = presheafRes P h.le x := rfl

variable {P} in

theorem app_presheafRes (φ : P ⟶ Q) {W W' : Opens T} (h : W' ≤ W) (x : P.obj (op W)) :
    (φ.app (op W')).hom (presheafRes P h x) = presheafRes Q h ((φ.app (op W)).hom x) :=
  congr(($(φ.naturality (homOfLE h).op)).hom x)

variable (V : Opens T) (U : ι → Opens T)

def presheafCube : Cube.{v} ι R := cechOpenFunctor V U ⋙ P

theorem presheafCube_obj (s : Finset ι) :
    (presheafCube P V U).obj s = P.obj (op (cechOpen V U s)) := rfl

theorem res_presheafCube {s t : Finset ι} (h : s ⊆ t) :
    Cube.res (presheafCube P V U) h = presheafRes P (cechOpen_anti V U h) := rfl

variable {P} in

def presheafCubeMap (φ : P ⟶ Q) : presheafCube P V U ⟶ presheafCube Q V U :=
  Functor.whiskerLeft (cechOpenFunctor V U) φ

variable {P} in

@[simp]
theorem presheafCubeMap_app (φ : P ⟶ Q) (s : Finset ι) :
    (presheafCubeMap V U φ).app s = φ.app (op (cechOpen V U s)) := rfl

variable (R) in

@[simps]
def presheafCubeFunctor : ((Opens T)ᵒᵖ ⥤ ModuleCat.{v} R) ⥤ Cube.{v} ι R where
  obj P := presheafCube P V U
  map := presheafCubeMap V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance presheafCubeFunctor_additive : (presheafCubeFunctor.{w, v} R V U).Additive where
  map_add := rfl

section Restrict

variable {V U} {V' V'' : Opens T} {U' U'' : ι → Opens T}

def presheafCubeRes (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) :
    presheafCube P V U ⟶ presheafCube P V' U' :=
  Cube.homMk (fun s => presheafRes P (h s)) fun hst x =>
    (presheafRes_presheafRes P _ _ x).trans
      (presheafRes_presheafRes P _ (cechOpen_anti V' U' hst) x).symm

@[simp]
theorem presheafCubeRes_app (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) (s : Finset ι) :
    ((presheafCubeRes P h).app s).hom = presheafRes P (h s) := rfl

theorem presheafCubeRes_self (h : ∀ s, cechOpen V U s ≤ cechOpen V U s) :
    presheafCubeRes P h = 𝟙 _ :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext (presheafRes_self P (h s))))

@[reassoc]
theorem presheafCubeRes_comp (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s)
    (h' : ∀ s, cechOpen V'' U'' s ≤ cechOpen V' U' s) :
    presheafCubeRes P h ≫ presheafCubeRes P h' = presheafCubeRes P fun s => (h' s).trans (h s) :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext
    (LinearMap.ext (presheafRes_presheafRes P (h s) (h' s))))

variable {P} in

@[reassoc]
theorem presheafCubeRes_naturality (φ : P ⟶ Q) (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) :
    presheafCubeMap V U φ ≫ presheafCubeRes Q h = presheafCubeRes P h ≫ presheafCubeMap V' U' φ :=
  NatTrans.ext (funext fun s => (φ.naturality (homOfLE (h s)).op).symm)

def presheafCubeCongr (h : ∀ s, cechOpen V U s = cechOpen V' U' s) :
    presheafCube P V U ≅ presheafCube P V' U' where
  hom := presheafCubeRes P fun s => (h s).ge
  inv := presheafCubeRes P fun s => (h s).le
  hom_inv_id := (presheafCubeRes_comp P _ _).trans (presheafCubeRes_self P _)
  inv_hom_id := (presheafCubeRes_comp P _ _).trans (presheafCubeRes_self P _)

end Restrict

def presheafCubeEmptyEquiv : P.obj (op V) ≃ₗ[R] (presheafCube P V U).obj ∅ :=
  presheafCongr P (cechOpen_empty V U).symm

theorem presheafCubeEmptyEquiv_apply (x : P.obj (op V)) :
    presheafCubeEmptyEquiv P V U x = presheafRes P (cechOpen_le V U ∅) x := rfl

variable [LinearOrder ι]

section Faces

variable [LinearOrder κ] (e : κ ↪o ι) (i : ι)

def presheafCubeLowerFaceIso :
    Cube.lowerFace e (presheafCube P V U) ≅ presheafCube P V fun k => U (e k) :=
  Cube.isoMk (fun s => presheafCongr P (cechOpen_map V U e.toEmbedding s)) fun hst x =>
    (presheafRes_presheafRes P _ _ x).trans
      (presheafRes_presheafRes P _ (cechOpen_anti V _ hst) x).symm

def presheafCubeUpperFaceIso :
    Cube.upperFace e i (presheafCube P V U) ≅ presheafCube P (V ⊓ U i) fun k => U (e k) :=
  Cube.isoMk (fun s => presheafCongr P (cechOpen_insert_map V U e.toEmbedding i s)) fun hst x =>
    (presheafRes_presheafRes P _ _ x).trans
      (presheafRes_presheafRes P _ (cechOpen_anti (V ⊓ U i) _ hst) x).symm

theorem presheafCubeLowerFaceIso_hom_app (s : Finset κ) :
    ((presheafCubeLowerFaceIso P V U e).hom.app s).hom =
      presheafRes P (cechOpen_map V U e.toEmbedding s).ge := rfl

theorem presheafCubeUpperFaceIso_hom_app (s : Finset κ) :
    ((presheafCubeUpperFaceIso P V U e i).hom.app s).hom =
      presheafRes P (cechOpen_insert_map V U e.toEmbedding i s).ge := rfl

@[reassoc]
theorem faceMap_presheafCube :
    Cube.faceMap e i (presheafCube P V U) ≫ (presheafCubeUpperFaceIso P V U e i).hom =
      (presheafCubeLowerFaceIso P V U e).hom ≫
        presheafCubeRes P (cechOpen_mono inf_le_left fun _ => le_rfl) :=
  NatTrans.ext (funext fun s => ModuleCat.hom_ext (LinearMap.ext fun x =>
    (presheafRes_presheafRes P _ _ x).trans
      (presheafRes_presheafRes P _ (cechOpen_mono inf_le_left (fun _ => le_rfl) s) x).symm))

end Faces

def presheafCech : CochainComplex (ModuleCat.{v} R) ℕ := cechComplex (presheafCube P V U)

def presheafCechH (n : ℕ) : ModuleCat.{v} R := (presheafCech P V U).homology n

theorem isZero_presheafCech_X [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    IsZero ((presheafCech P V U).X n) := isZero_cechComplex_X _ h

theorem isZero_presheafCechH [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    IsZero (presheafCechH P V U n) := isZero_cechComplex_homology _ h

variable {V U} in

theorem isIso_cechComplexMap_presheafCubeRes {V' : Opens T} {U' : ι → Opens T}
    (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s)
    (h' : ∀ s, s.Nonempty → cechOpen V U s ≤ cechOpen V' U' s) :
    IsIso (cechComplexMap (presheafCubeRes P h)) :=
  isIso_cechComplexMap _ fun s hs => presheafRes_bijective P (h s) (h' s hs)

variable {V U} in

def presheafCechTopIso (h : ∀ i, U i ≤ V) : presheafCech P ⊤ U ≅ presheafCech P V U :=
  @asIso _ _ _ _
    (cechComplexMap (presheafCubeRes P (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)))
    (isIso_cechComplexMap_presheafCubeRes P _
      fun _ hs => ((cechOpen_top U _).trans (cechOpen_of_nonempty h hs).symm).le)

variable {V U} in

theorem presheafCechTopIso_hom (h : ∀ i, U i ≤ V) : (presheafCechTopIso P h).hom =
    cechComplexMap (presheafCubeRes P (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)) := rfl

omit [LinearOrder ι] in

def presheafCechAug : P.obj (op V) →ₗ[R] Cube.Term (presheafCube P V U) 1 :=
  LinearMap.pi fun s => presheafRes P (cechOpen_le V U s.1)

omit [LinearOrder ι] in

@[simp]
theorem presheafCechAug_apply (x : P.obj (op V)) (s : {s : Finset ι // s.card = 1}) :
    presheafCechAug P V U x s = presheafRes P (cechOpen_le V U s.1) x := rfl

omit [LinearOrder ι] in

theorem aug_presheafCubeEmptyEquiv (x : P.obj (op V)) :
    Cube.aug (presheafCube P V U) (presheafCubeEmptyEquiv P V U x) = presheafCechAug P V U x :=
  funext fun _ => presheafRes_presheafRes P _ _ x

@[simp]
theorem d_presheafCechAug (x : P.obj (op V)) :
    Cube.d (presheafCube P V U) 1 (presheafCechAug P V U x) = 0 := by
  rw [← aug_presheafCubeEmptyEquiv, Cube.d_aug]

def presheafToCechH : P.obj (op V) →ₗ[R] presheafCechH P V U 0 :=
  (cechAugHomology (presheafCube P V U)).hom ∘ₗ (presheafCubeEmptyEquiv P V U).toLinearMap

theorem presheafToCechH_apply (x : P.obj (op V)) :
    presheafToCechH P V U x =
      cechClass (presheafCube P V U) 0 ⟨presheafCechAug P V U x, d_presheafCechAug P V U x⟩ :=
  (cechAugHomology_apply _ _).trans
    (congrArg _ (Subtype.ext (aug_presheafCubeEmptyEquiv P V U x)))

variable {P} in

theorem homologyMap_presheafToCechH (φ : P ⟶ Q) (x : P.obj (op V)) :
    (HomologicalComplex.homologyMap (cechComplexMap (presheafCubeMap V U φ)) 0).hom
      (presheafToCechH P V U x) = presheafToCechH Q V U ((φ.app (op V)).hom x) := by
  rw [presheafToCechH_apply, presheafToCechH_apply]
  exact homologyMap_cechClass _ 0 _ _ (funext fun _ => app_presheafRes φ _ x)

variable {V U} in

theorem homologyMap_res_presheafToCechH {V' : Opens T} {U' : ι → Opens T}
    (h : ∀ s, cechOpen V' U' s ≤ cechOpen V U s) (hV : V' ≤ V) (x : P.obj (op V)) :
    (HomologicalComplex.homologyMap (cechComplexMap (presheafCubeRes P h)) 0).hom
      (presheafToCechH P V U x) = presheafToCechH P V' U' (presheafRes P hV x) := by
  rw [presheafToCechH_apply, presheafToCechH_apply]
  exact homologyMap_cechClass _ 0 _ _ (funext fun s =>
    (presheafRes_presheafRes P _ _ x).trans
      (presheafRes_presheafRes P hV (cechOpen_le V' U' s.1) x).symm)

theorem presheafRes_eq_of_d_eq_zero (x : Cube.Term (presheafCube P V U) 1)
    (hx : Cube.d (presheafCube P V U) 1 x = 0) (i j : ι) {W : Opens T}
    (hi : W ≤ cechOpen V U {i}) (hj : W ≤ cechOpen V U {j}) :
    presheafRes P hi (x ⟨{i}, Finset.card_singleton i⟩) =
      presheafRes P hj (x ⟨{j}, Finset.card_singleton j⟩) := by
  wlog hij : i < j generalizing i j
  · rcases (not_lt.1 hij).eq_or_lt with rfl | h
    · rfl
    · exact (this j i hj hi h).symm
  have hW : W ≤ cechOpen V U {i, j} :=
    (le_inf hi hj).trans (cechOpen_union V U {i} {j}).ge
  have h := (Cube.d_one_apply_pair _ x hij).symm.trans (congrFun hx _)
  have h' := congrArg (presheafRes P hW) (sub_eq_zero.1 h)
  exact (presheafRes_presheafRes P _ hW _).symm.trans
    (h'.symm.trans (presheafRes_presheafRes P _ hW _))

end Presheaf

section Sheaf

variable {T : TopCat.{w}} {ι : Type} {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  {V : Opens T} {U : ι → Opens T} (hc : V ≤ ⨆ i, U i)

include hP hc

theorem presheafCechAug_injective : Function.Injective (presheafCechAug P V U) := fun x y h =>
  TopCat.Sheaf.eq_of_locally_eq' (C := ModuleCat.{w} R) ⟨P, hP⟩ (fun i => cechOpen V U {i}) V
    (fun i => homOfLE (cechOpen_le V U {i}))
    ((cechOpen_empty V U).ge.trans (cechOpen_empty_le_iSup hc)) x y
    fun i => congrFun h ⟨{i}, Finset.card_singleton i⟩

variable [LinearOrder ι]

theorem presheafCechAug_exact :
    Function.Exact (presheafCechAug P V U) (Cube.d (presheafCube P V U) 1) := by
  intro x
  refine ⟨fun hx => ?_, by rintro ⟨y, rfl⟩; exact d_presheafCechAug P V U y⟩
  obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing' (C := ModuleCat.{w} R) ⟨P, hP⟩
    (fun i => cechOpen V U {i}) V (fun i => homOfLE (cechOpen_le V U {i}))
    ((cechOpen_empty V U).ge.trans (cechOpen_empty_le_iSup hc))
    (fun i => x ⟨{i}, Finset.card_singleton i⟩)
    fun i j => presheafRes_eq_of_d_eq_zero P V U x hx i j inf_le_left inf_le_right
  exact ⟨y, (Cube.termOneEquiv _).symm.injective (funext hy)⟩

theorem presheafToCechH_bijective : Function.Bijective (presheafToCechH P V U) := by
  constructor
  · intro x y h
    rw [presheafToCechH_apply, presheafToCechH_apply] at h
    exact presheafCechAug_injective hP hc
      (congrArg Subtype.val ((cechClass_zero_bijective _).1 h))
  · intro z
    obtain ⟨⟨x, hx⟩, rfl⟩ := cechClass_surjective (presheafCube P V U) 0 z
    obtain ⟨y, rfl⟩ := (presheafCechAug_exact hP hc x).1 hx
    exact ⟨y, presheafToCechH_apply P V U y⟩

theorem isIso_cechAugHomology_presheafCube : IsIso (cechAugHomology (presheafCube P V U)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Function.Bijective.of_comp_iff _ (presheafCubeEmptyEquiv P V U).bijective).1
    (presheafToCechH_bijective hP hc)

theorem presheafCube_exactAt_zero_one :
    (cubeComplex (presheafCube P V U)).ExactAt 0 ∧ (cubeComplex (presheafCube P V U)).ExactAt 1 :=
  (isIso_cechAugHomology_iff _).1 (isIso_cechAugHomology_presheafCube hP hc)

def presheafCechHZeroEquiv : presheafCechH P V U 0 ≃ₗ[R] P.obj (op V) :=
  (LinearEquiv.ofBijective _ (presheafToCechH_bijective hP hc)).symm

@[simp]
theorem presheafCechHZeroEquiv_symm_apply (x : P.obj (op V)) :
    (presheafCechHZeroEquiv hP hc).symm x = presheafToCechH P V U x := rfl

end Sheaf

@[simps]
def abToIntModule : AddCommGrpCat.{v} ⥤ ModuleCat.{v} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap

instance abToIntModule_additive : abToIntModule.{v}.Additive where
  map_add := rfl

section Ab

variable {T : Type w} [TopologicalSpace T] {ι : Type}
  (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) {Q Q' : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}}
  (V : Opens T) (U : ι → Opens T)

def cechAbCube : Cube.{v} ι ℤ := presheafCube (P ⋙ abToIntModule) V U

theorem cechAbCube_obj (s : Finset ι) :
    (cechAbCube P V U).obj s = ModuleCat.of ℤ (P.obj (op (cechOpen V U s))) := rfl

theorem res_cechAbCube {s t : Finset ι} (h : s ⊆ t) (x : P.obj (op (cechOpen V U s))) :
    Cube.res (cechAbCube P V U) h x = P.map (homOfLE (cechOpen_anti V U h)).op x := rfl

variable {P} in

def cechAbCubeMap (φ : P ⟶ Q) : cechAbCube P V U ⟶ cechAbCube Q V U :=
  presheafCubeMap V U (Functor.whiskerRight φ abToIntModule)

variable {P} in

@[simp]
theorem cechAbCubeMap_app_apply (φ : P ⟶ Q) (s : Finset ι) (x : P.obj (op (cechOpen V U s))) :
    ((cechAbCubeMap V U φ).app s).hom x = φ.app (op (cechOpen V U s)) x := rfl

@[simps]
def cechAbCubeFunctor : ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ Cube.{v} ι ℤ where
  obj P := cechAbCube P V U
  map := cechAbCubeMap V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance cechAbCubeFunctor_additive : (cechAbCubeFunctor.{w, v} V U).Additive where
  map_add := rfl

variable [LinearOrder ι]

def cechAb : CochainComplex (ModuleCat.{v} ℤ) ℕ := cechComplex (cechAbCube P V U)

def cechAbH (n : ℕ) : ModuleCat.{v} ℤ := (cechAb P V U).homology n

theorem cechAb_X (p : ℕ) : (cechAb P V U).X p =
    ModuleCat.of ℤ (∀ s : {s : Finset ι // s.card = p + 1}, P.obj (op (cechOpen V U s.1))) := rfl

theorem cechAb_d (p : ℕ) :
    (cechAb P V U).d p (p + 1) = ModuleCat.ofHom (Cube.d (cechAbCube P V U) (p + 1)) :=
  cechComplex_d _ p

variable {P} in

def cechAbMap (φ : P ⟶ Q) : cechAb P V U ⟶ cechAb Q V U := cechComplexMap (cechAbCubeMap V U φ)

variable {P} in

def cechAbHMap (φ : P ⟶ Q) (n : ℕ) : cechAbH P V U n ⟶ cechAbH Q V U n :=
  HomologicalComplex.homologyMap (cechAbMap V U φ) n

@[simps]
def cechAbFunctor : ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ CochainComplex (ModuleCat.{v} ℤ) ℕ where
  obj P := cechAb P V U
  map := cechAbMap V U
  map_id _ := rfl
  map_comp _ _ := rfl

instance cechAbFunctor_additive : (cechAbFunctor.{w, v} V U).Additive where
  map_add := rfl

@[simps]
def cechAbHFunctor (n : ℕ) : ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ ModuleCat.{v} ℤ where
  obj P := cechAbH P V U n
  map φ := cechAbHMap V U φ n
  map_id P := (cechAbFunctor V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_id P
  map_comp := (cechAbFunctor V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_comp

instance cechAbHFunctor_additive (n : ℕ) : (cechAbHFunctor.{w, v} V U n).Additive where
  map_add := (cechAbFunctor V U ⋙ HomologicalComplex.homologyFunctor _ _ n).map_add

@[simp]
theorem cechAbHMap_id (n : ℕ) : cechAbHMap V U (𝟙 P) n = 𝟙 _ := (cechAbHFunctor V U n).map_id P

variable {P} in

@[reassoc]
theorem cechAbHMap_comp (φ : P ⟶ Q) (ψ : Q ⟶ Q') (n : ℕ) :
    cechAbHMap V U (φ ≫ ψ) n = cechAbHMap V U φ n ≫ cechAbHMap V U ψ n :=
  (cechAbHFunctor V U n).map_comp φ ψ

variable {P} in

theorem cechAbHMap_add (φ ψ : P ⟶ Q) (n : ℕ) :
    cechAbHMap V U (φ + ψ) n = cechAbHMap V U φ n + cechAbHMap V U ψ n :=
  (cechAbHFunctor V U n).map_add

theorem cechAbFunctor_shortExact (S : ShortComplex ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v}))
    (h : ∀ s : Finset ι, s.Nonempty →
      Function.Injective (S.f.app (op (cechOpen V U s))) ∧
      Function.Exact (S.f.app (op (cechOpen V U s))) (S.g.app (op (cechOpen V U s))) ∧
      Function.Surjective (S.g.app (op (cechOpen V U s)))) :
    (S.map (cechAbFunctor V U)).ShortExact :=
  cechFunctor_shortExact (S.map (cechAbCubeFunctor V U)) fun s hs =>
    ModuleCat.shortComplex_shortExact _ (h s hs).2.1 (h s hs).1 (h s hs).2.2

theorem isZero_cechAb_X [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    IsZero ((cechAb P V U).X n) := isZero_cechComplex_X _ h

theorem isZero_cechAbH [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    IsZero (cechAbH P V U n) := isZero_cechComplex_homology _ h

theorem subsingleton_cechAbH [Fintype ι] {n : ℕ} (h : Fintype.card ι ≤ n) :
    Subsingleton (cechAbH P V U n) := ModuleCat.isZero_iff_subsingleton.1 (isZero_cechAbH P V U h)

variable {V U} in

def cechAbTopIso (h : ∀ i, U i ≤ V) : cechAb P ⊤ U ≅ cechAb P V U :=
  presheafCechTopIso (P ⋙ abToIntModule) h

def toCechAbH : P.obj (op V) →ₗ[ℤ] cechAbH P V U 0 := presheafToCechH (P ⋙ abToIntModule) V U

variable {P} in

theorem cechAbHMap_toCechAbH (φ : P ⟶ Q) (x : P.obj (op V)) :
    (cechAbHMap V U φ 0).hom (toCechAbH P V U x) = toCechAbH Q V U (φ.app (op V) x) :=
  homologyMap_presheafToCechH V U (Functor.whiskerRight φ abToIntModule) x

end Ab

section AbSheaf

variable {T : TopCat.{w}} {ι : Type} {P Q : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{w}}
  {V : Opens T} {U : ι → Opens T}

theorem isSheaf_comp_abToIntModule (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P) :
    Presheaf.IsSheaf (Opens.grothendieckTopology T) (P ⋙ abToIntModule) :=
  (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := ModuleCat.{w} ℤ) (X := T)
    (P ⋙ abToIntModule)).2
    ((TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (C := AddCommGrpCat.{w}) (X := T) P).1 hP)

variable [LinearOrder ι]

theorem cechAbCube_exactAt_zero_one (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
    (hc : V ≤ ⨆ i, U i) :
    (cubeComplex (cechAbCube P V U)).ExactAt 0 ∧ (cubeComplex (cechAbCube P V U)).ExactAt 1 :=
  presheafCube_exactAt_zero_one (isSheaf_comp_abToIntModule hP) hc

def cechAbHZeroEquiv (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
    (hc : V ≤ ⨆ i, U i) : cechAbH P V U 0 ≃ₗ[ℤ] P.obj (op V) :=
  presheafCechHZeroEquiv (isSheaf_comp_abToIntModule hP) hc

@[simp]
theorem cechAbHZeroEquiv_symm_apply (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
    (hc : V ≤ ⨆ i, U i) (x : P.obj (op V)) :
    (cechAbHZeroEquiv hP hc).symm x = toCechAbH P V U x := rfl

theorem cechAbHZeroEquiv_map (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
    (hQ : Presheaf.IsSheaf (Opens.grothendieckTopology T) Q) (hc : V ≤ ⨆ i, U i) (φ : P ⟶ Q)
    (x : cechAbH P V U 0) :
    cechAbHZeroEquiv hQ hc ((cechAbHMap V U φ 0).hom x) =
      φ.app (op V) (cechAbHZeroEquiv hP hc x) := by
  obtain ⟨y, rfl⟩ := (cechAbHZeroEquiv hP hc).symm.surjective x
  rw [LinearEquiv.apply_symm_apply, cechAbHZeroEquiv_symm_apply, cechAbHMap_toCechAbH,
    ← cechAbHZeroEquiv_symm_apply hQ hc, LinearEquiv.apply_symm_apply]

end AbSheaf

end GlobalTheory
