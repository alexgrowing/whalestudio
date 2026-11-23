import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res homOfLinear homOfLinear_app isoOfLinear toMod fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover germ_resM)
open GlobalTheory.QCoh (IsFiniteQC appLinear appLinear_apply stalkLinear freeModule)

namespace GlobalTheory.VB

variable {X Y : Scheme.{0}} {F G H : X.Modules} {U V W : X.Opens} {ι : Type} [Fintype ι]

variable (F G V) in

def homGroup :
    AddSubgroup (∀ W : {W : X.Opens // W ≤ V}, Γ(F, W.1) →ₗ[Γ(X, W.1)] Γ(G, W.1)) where
  carrier := {φ | ∀ (W W' : X.Opens) (h : W ≤ V) (h' : W' ≤ W) (s : Γ(F, W)),
    φ ⟨W', h'.trans h⟩ (resM F h' s) = resM G h' (φ ⟨W, h⟩ s)}
  add_mem' := fun {φ ψ} hφ hψ W W' h h' s => by
    simp only [Pi.add_apply, LinearMap.add_apply, map_add, hφ W W' h h', hψ W W' h h']
  zero_mem' := fun W W' h h' s => by simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero]
  neg_mem' := fun {φ} hφ W W' h h' s => by
    simp only [Pi.neg_apply, LinearMap.neg_apply, map_neg, hφ W W' h h']

instance homGroupModule : Module Γ(X, V) (homGroup F G V) where
  smul a φ := ⟨fun W => resG X W.2 a • φ.1 W, fun W W' h h' s => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, φ.2 W W' h h', resM_smul, resG_resG]⟩
  one_smul φ := Subtype.ext <| funext fun ⟨W, h⟩ => by
    change resG X h 1 • φ.1 ⟨W, h⟩ = _
    rw [map_one, one_smul]
  mul_smul a b φ := Subtype.ext <| funext fun ⟨W, h⟩ => by
    change resG X h (a * b) • φ.1 ⟨W, h⟩ = resG X h a • resG X h b • φ.1 ⟨W, h⟩
    rw [map_mul, mul_smul]
  smul_zero a := Subtype.ext <| funext fun ⟨W, h⟩ => smul_zero (resG X h a)
  smul_add a φ ψ := Subtype.ext <| funext fun ⟨W, h⟩ => smul_add (resG X h a) _ _
  add_smul a b φ := Subtype.ext <| funext fun ⟨W, h⟩ => by
    change resG X h (a + b) • φ.1 ⟨W, h⟩ = resG X h a • φ.1 ⟨W, h⟩ + resG X h b • φ.1 ⟨W, h⟩
    rw [map_add, add_smul]
  zero_smul φ := Subtype.ext <| funext fun ⟨W, h⟩ => by
    change resG X h 0 • φ.1 ⟨W, h⟩ = 0
    rw [map_zero, zero_smul]

variable (F G) in

def homRes (h : W ≤ V) : homGroup F G V →+ homGroup F G W where
  toFun φ := ⟨fun T => φ.1 ⟨T.1, T.2.trans h⟩, fun T T' hT h' s => φ.2 T T' (hT.trans h) h' s⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable (F G) in

def homPresheaf : TopCat.Presheaf Ab.{0} X where
  obj V := AddCommGrpCat.of (homGroup F G V.unop)
  map f := AddCommGrpCat.ofHom (homRes F G (leOfHom f.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

variable (F G) in

theorem isSheaf_homPresheaf : (homPresheaf F G).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  let φ : ∀ i, homGroup F G (U i) := fun i => sf i
  have hc : ∀ (i j : ι) (T : X.Opens) (hi : T ≤ U i) (hj : T ≤ U j),
      (φ i).1 ⟨T, hi⟩ = (φ j).1 ⟨T, hj⟩ := fun i j T hi hj =>
    congrArg (fun χ : homGroup F G (U i ⊓ U j) => χ.1 ⟨T, le_inf hi hj⟩) (hsf i j)
  have hcov : ∀ W : X.Opens, W ≤ iSup U → W ≤ ⨆ i, W ⊓ U i := fun W hW => by
    rw [← inf_iSup_eq]
    exact le_inf le_rfl hW
  have hex : ∀ (W : X.Opens) (hW : W ≤ iSup U) (s : Γ(F, W)), ∃ g : Γ(G, W),
      ∀ i, resM G (inf_le_left : W ⊓ U i ≤ W) g =
        (φ i).1 ⟨W ⊓ U i, inf_le_right⟩ (resM F (inf_le_left : W ⊓ U i ≤ W) s) := by
    intro W hW s
    have ht : ∀ (k : ι) (T : X.Opens) (hT : T ≤ W ⊓ U k),
        resM G hT ((φ k).1 ⟨W ⊓ U k, inf_le_right⟩ (resM F (inf_le_left : W ⊓ U k ≤ W) s)) =
          (φ k).1 ⟨T, hT.trans inf_le_right⟩ (resM F (hT.trans inf_le_left) s) := by
      intro k T hT
      rw [← (φ k).2 (W ⊓ U k) T inf_le_right hT, resM_resM]
    obtain ⟨g, hg⟩ := exists_sec_of_cover (F := G) (fun i => W ⊓ U i) (fun i => inf_le_left) (hcov W hW)
      (fun k => (φ k).1 ⟨W ⊓ U k, inf_le_right⟩ (resM F (inf_le_left : W ⊓ U k ≤ W) s))
      (fun k l => by
        try dsimp only
        rw [ht, ht]
        exact LinearMap.congr_fun (hc k l _ _ _) _)
    exact ⟨g, hg⟩
  choose g hg using hex
  have key : ∀ (W : X.Opens) (hW : W ≤ iSup U) (s : Γ(F, W)) (i : ι) (T : X.Opens) (hT : T ≤ W)
      (hTi : T ≤ U i), resM G hT (g W hW s) = (φ i).1 ⟨T, hTi⟩ (resM F hT s) := by
    intro W hW s i T hT hTi
    have h1 : T ≤ W ⊓ U i := le_inf hT hTi
    calc resM G hT (g W hW s)
        = resM G h1 (resM G (inf_le_left : W ⊓ U i ≤ W) (g W hW s)) := (resM_resM _ _ _).symm
      _ = resM G h1 ((φ i).1 ⟨W ⊓ U i, inf_le_right⟩ (resM F (inf_le_left : W ⊓ U i ≤ W) s)) := by
          rw [hg W hW s i]
      _ = (φ i).1 ⟨T, h1.trans inf_le_right⟩ (resM F h1 (resM F (inf_le_left : W ⊓ U i ≤ W) s)) :=
          ((φ i).2 _ _ _ _ _).symm
      _ = (φ i).1 ⟨T, hTi⟩ (resM F hT s) := by rw [resM_resM]
  have gcomp : ∀ (W W' : X.Opens) (h : W ≤ iSup U) (h' : W' ≤ W) (s : Γ(F, W)),
      g W' (h'.trans h) (resM F h' s) = resM G h' (g W h s) := by
    intro W W' h h' s
    refine sec_ext_of_cover (fun i => W' ⊓ U i) (fun i => inf_le_left) (hcov W' (h'.trans h)) fun i => ?_
    simp only [resM_resM]
    rw [key W' (h'.trans h) (resM F h' s) i (W' ⊓ U i) inf_le_left inf_le_right,
      key W h s i (W' ⊓ U i) (inf_le_left.trans h') inf_le_right, resM_resM]
  have gadd : ∀ (W : X.Opens) (hW : W ≤ iSup U) (s s' : Γ(F, W)),
      g W hW (s + s') = g W hW s + g W hW s' := by
    intro W hW s s'
    refine sec_ext_of_cover (fun i => W ⊓ U i) (fun i => inf_le_left) (hcov W hW) fun i => ?_
    rw [map_add, key W hW (s + s') i (W ⊓ U i) inf_le_left inf_le_right,
      key W hW s i (W ⊓ U i) inf_le_left inf_le_right, key W hW s' i (W ⊓ U i) inf_le_left inf_le_right,
      map_add, map_add]
  have gsmul : ∀ (W : X.Opens) (hW : W ≤ iSup U) (a : Γ(X, W)) (s : Γ(F, W)),
      g W hW (a • s) = a • g W hW s := by
    intro W hW a s
    refine sec_ext_of_cover (fun i => W ⊓ U i) (fun i => inf_le_left) (hcov W hW) fun i => ?_
    rw [resM_smul, key W hW (a • s) i (W ⊓ U i) inf_le_left inf_le_right,
      key W hW s i (W ⊓ U i) inf_le_left inf_le_right, resM_smul, map_smul]
  let ψ : homGroup F G (iSup U) := ⟨fun W =>
    { toFun := g W.1 W.2
      map_add' := gadd W.1 W.2
      map_smul' := gsmul W.1 W.2 }, fun W W' h h' s => gcomp W W' h h' s⟩
  refine ⟨ψ, fun i => ?_, fun ψ' hψ' => ?_⟩
  · change @Eq ↥(homGroup F G (U i)) (homRes F G (le_iSup U i) ψ) (φ i)
    refine Subtype.ext (funext fun T => LinearMap.ext fun s => ?_)
    have := key T.1 (T.2.trans (le_iSup U i)) s i T.1 le_rfl T.2
    rw [resM_self, resM_self] at this
    exact this
  · change homGroup F G (iSup U) at ψ'
    change @Eq ↥(homGroup F G (iSup U)) ψ' ψ
    refine Subtype.ext (funext fun W => LinearMap.ext fun s => ?_)
    refine sec_ext_of_cover (fun i => W.1 ⊓ U i) (fun i => inf_le_left) (hcov W.1 W.2) fun i => ?_
    have h1 := ψ'.2 W.1 (W.1 ⊓ U i) W.2 inf_le_left s
    have h2 : ψ'.1 ⟨W.1 ⊓ U i, inf_le_left.trans W.2⟩ (resM F (inf_le_left : W.1 ⊓ U i ≤ W.1) s) =
        (φ i).1 ⟨W.1 ⊓ U i, inf_le_right⟩ (resM F (inf_le_left : W.1 ⊓ U i ≤ W.1) s) :=
      congrArg (fun χ : homGroup F G (U i) =>
        χ.1 ⟨W.1 ⊓ U i, inf_le_right⟩ (resM F (inf_le_left : W.1 ⊓ U i ≤ W.1) s)) (hψ' i)
    rw [← h1, h2]
    exact (key W.1 W.2 s i _ inf_le_left inf_le_right).symm

variable (F G) in

def homMod : X.Modules :=
  letI : ∀ V, Module (X.ringCatSheaf.obj.obj V) ((homPresheaf F G).obj V) :=
    fun V => homGroupModule (V := V.unop)
  { val := PresheafOfModules.ofPresheaf (homPresheaf F G) fun _ _ f r φ =>
      Subtype.ext (funext fun T =>
        congrArg (· • φ.1 ⟨T.1, T.2.trans (leOfHom f.unop)⟩)
          (resG_resG (leOfHom f.unop) T.2 r).symm)
    isSheaf := isSheaf_homPresheaf F G }

def homApp (φ : Γ(homMod F G, V)) (h : W ≤ V) : Γ(F, W) →ₗ[Γ(X, W)] Γ(G, W) :=
  (show homGroup F G V from φ).1 ⟨W, h⟩

theorem homApp_resM (φ : Γ(homMod F G, V)) (h : W ≤ V) {T : X.Opens} (h' : T ≤ W) (s : Γ(F, W)) :
    homApp φ (h'.trans h) (resM F h' s) = resM G h' (homApp φ h s) := by
  exact (show homGroup F G V from φ).2 W T h h' s

def homMk (φ : ∀ W : X.Opens, W ≤ V → (Γ(F, W) →ₗ[Γ(X, W)] Γ(G, W)))
    (hφ : ∀ (W W' : X.Opens) (h : W ≤ V) (h' : W' ≤ W) (s : Γ(F, W)),
      φ W' (h'.trans h) (resM F h' s) = resM G h' (φ W h s)) : Γ(homMod F G, V) :=
  (⟨fun W => φ W.1 W.2, hφ⟩ : homGroup F G V)

@[simp] theorem homApp_homMk (φ : ∀ W : X.Opens, W ≤ V → (Γ(F, W) →ₗ[Γ(X, W)] Γ(G, W))) (hφ)
    (h : W ≤ V) : homApp (homMk φ hφ) h = φ W h := rfl

@[ext] theorem hom_ext {φ ψ : Γ(homMod F G, V)}
    (e : ∀ (W : X.Opens) (h : W ≤ V) (s : Γ(F, W)), homApp φ h s = homApp ψ h s) : φ = ψ := by
  have key := @Subtype.ext _ _ (show homGroup F G V from φ) (show homGroup F G V from ψ)
    (funext fun T => LinearMap.ext (e T.1 T.2))
  exact key

@[simp] theorem homApp_zero (h : W ≤ V) : homApp (0 : Γ(homMod F G, V)) h = 0 := rfl

@[simp] theorem homApp_add (φ ψ : Γ(homMod F G, V)) (h : W ≤ V) :
    homApp (φ + ψ) h = homApp φ h + homApp ψ h := rfl

@[simp] theorem homApp_smul (a : Γ(X, V)) (φ : Γ(homMod F G, V)) (h : W ≤ V) :
    homApp (a • φ) h = resG X h a • homApp φ h := rfl

theorem homApp_sum {κ : Type*} (t : Finset κ) (φ : κ → Γ(homMod F G, V)) (h : W ≤ V) :
    homApp (∑ k ∈ t, φ k) h = ∑ k ∈ t, homApp (φ k) h := by
  classical
  refine Finset.induction_on t (by simp only [Finset.sum_empty, homApp_zero]) ?_
  intro a t ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, homApp_add, ih]

@[simp] theorem homApp_res (φ : Γ(homMod F G, V)) (h : W ≤ V) {T : X.Opens} (h' : T ≤ W) :
    homApp (resM (homMod F G) h φ) h' = homApp φ (h'.trans h) := rfl

variable (F G) in

def homGlobalEquiv : Γ(homMod F G, ⊤) ≃+ (F ⟶ G) where
  toFun φ := homOfLinear (fun _ => homApp φ le_top) fun h s => homApp_resM φ le_top h s
  invFun φ := homMk (fun W _ => appLinear φ W) fun _ _ _ h s => app_resM φ h s
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp] theorem homGlobalEquiv_app (φ : Γ(homMod F G, ⊤)) (s : Γ(F, V)) :
    (homGlobalEquiv F G φ).app V s = homApp φ le_top s := rfl

def homMap {F' G' : X.Modules} (α : F' ⟶ F) (β : G ⟶ G') : homMod F G ⟶ homMod F' G' :=
  homOfLinear (fun V =>
    { toFun φ := homMk (fun W h => appLinear β W ∘ₗ homApp φ h ∘ₗ appLinear α W)
        fun W W' h h' s => by
          simp only [LinearMap.comp_apply, appLinear_apply, app_resM, homApp_resM φ h h']
      map_add' := fun φ ψ => hom_ext fun W h s => map_add (appLinear β W) _ _
      map_smul' := fun a φ => hom_ext fun W h s => map_smul (appLinear β W) _ _ })
    fun _ _ => rfl

@[simp] theorem homApp_homMap {F' G' : X.Modules} (α : F' ⟶ F) (β : G ⟶ G')
    (φ : Γ(homMod F G, V)) (h : W ≤ V) (s : Γ(F', W)) :
    homApp ((homMap α β).app V φ) h s = β.app W (homApp φ h (α.app W s)) := rfl

variable (F) in

def dual : X.Modules := homMod F (structureModule X)

def dualApp (l : Γ(dual F, V)) (h : W ≤ V) : Γ(F, W) →ₗ[Γ(X, W)] Γ(X, W) := homApp l h

theorem dualApp_resM (l : Γ(dual F, V)) (h : W ≤ V) {T : X.Opens} (h' : T ≤ W) (s : Γ(F, W)) :
    dualApp l (h'.trans h) (resM F h' s) = resG X h' (dualApp l h s) := by
  exact homApp_resM l h h' s

def dualMk (l : ∀ W : X.Opens, W ≤ V → (Γ(F, W) →ₗ[Γ(X, W)] Γ(X, W)))
    (hl : ∀ (W W' : X.Opens) (h : W ≤ V) (h' : W' ≤ W) (s : Γ(F, W)),
      l W' (h'.trans h) (resM F h' s) = resG X h' (l W h s)) : Γ(dual F, V) :=
  homMk (G := structureModule X) l hl

@[simp] theorem dualApp_dualMk (l : ∀ W : X.Opens, W ≤ V → (Γ(F, W) →ₗ[Γ(X, W)] Γ(X, W))) (hl)
    (h : W ≤ V) : dualApp (dualMk l hl) h = l W h := rfl

@[ext] theorem dual_ext {l l' : Γ(dual F, V)}
    (e : ∀ (W : X.Opens) (h : W ≤ V) (s : Γ(F, W)), dualApp l h s = dualApp l' h s) : l = l' := by
  exact hom_ext e

@[simp] theorem dualApp_zero (h : W ≤ V) : dualApp (0 : Γ(dual F, V)) h = 0 := rfl

@[simp] theorem dualApp_add (l l' : Γ(dual F, V)) (h : W ≤ V) :
    dualApp (l + l') h = dualApp l h + dualApp l' h := rfl

@[simp] theorem dualApp_smul (a : Γ(X, V)) (l : Γ(dual F, V)) (h : W ≤ V) :
    dualApp (a • l) h = resG X h a • dualApp l h := rfl

theorem dualApp_sum {κ : Type*} (t : Finset κ) (l : κ → Γ(dual F, V)) (h : W ≤ V) :
    dualApp (∑ k ∈ t, l k) h = ∑ k ∈ t, dualApp (l k) h := by
  exact homApp_sum t l h

@[simp] theorem dualApp_res (l : Γ(dual F, V)) (h : W ≤ V) {T : X.Opens} (h' : T ≤ W) :
    dualApp (resM (dual F) h l) h' = dualApp l (h'.trans h) := rfl

def dualMap (φ : F ⟶ G) : dual G ⟶ dual F := homMap φ (𝟙 _)

@[simp] theorem dualApp_dualMap (φ : F ⟶ G) (l : Γ(dual G, V)) (h : W ≤ V) (s : Γ(F, W)) :
    dualApp ((dualMap φ).app V l) h s = dualApp l h (φ.app W s) := rfl

@[simp] theorem dualMap_id : dualMap (𝟙 F) = 𝟙 (dual F) := rfl

theorem dualMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) : dualMap (φ ≫ ψ) = dualMap ψ ≫ dualMap φ := rfl

theorem dualMap_add (φ ψ : F ⟶ G) : dualMap (φ + ψ) = dualMap φ + dualMap ψ := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext l W h s
  first
  | simp [dualApp_dualMap]
  | (rw [dualApp_dualMap]; simp)

@[simp] theorem dualMap_zero : dualMap (0 : F ⟶ G) = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext l W h s
  first
  | simp [dualApp_dualMap]
  | (rw [dualApp_dualMap]; simp)

@[simp] theorem dualMap_smulHom (a : Γ(X, ⊤)) : dualMap (smulHom F a) = smulHom (dual F) a := by
  have key : ∀ (M : X.Modules) (T : X.Opens) (x : Γ(M, T)),
      (smulHom M a).app T x = restrictGlobal X T a • x := fun M T x => rfl
  have key2 : ∀ T : X.Opens, restrictGlobal X T a = resG X le_top a := fun T => by
    first
    | rfl
    | simp [restrictGlobal, resG]
    | (unfold restrictGlobal resG; rfl)
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext l W h s
  rw [dualApp_dualMap, key, key, dualApp_smul, map_smul, LinearMap.smul_apply, key2, key2, resG_resG]

variable (X) in

@[simps] def dualFunctor : X.Modulesᵒᵖ ⥤ X.Modules where
  obj F := dual F.unop
  map φ := dualMap φ.unop

instance : (dualFunctor X).Additive where
  map_add := dualMap_add _ _

@[simps] def dualIso (φ : F ≅ G) : dual G ≅ dual F where
  hom := dualMap φ.hom
  inv := dualMap φ.inv
  hom_inv_id := by rw [← dualMap_comp, φ.inv_hom_id, dualMap_id]
  inv_hom_id := by rw [← dualMap_comp, φ.hom_inv_id, dualMap_id]

instance mono_dualMap (φ : F ⟶ G) [Epi φ] : Mono (dualMap φ) := by
  refine QCoh.mono_of_locally_app_injective _ fun V _ hx => ⟨V, hx, le_rfl,
    (injective_iff_map_eq_zero _).2 fun l hl => dual_ext fun W h s => ?_⟩
  have H (x : W) : ∃ (T : X.Opens) (h' : T ≤ W), x.1 ∈ T ∧ ∃ t, φ.app T t = resM G h' s := by
    obtain ⟨t, ht⟩ := QCoh.stalkLinear_surjective φ x.1 (G.presheaf.germ W x x.2 s)
    obtain ⟨T, hT, hxT, t, rfl⟩ := Twist.exists_germ_eq_of_mem x.2 t
    rw [QCoh.stalkLinear_germ, ← germ_resM hT hxT] at ht
    obtain ⟨T', hxT', i₁, i₂, e⟩ := G.presheaf.germ_eq x.1 hxT hxT _ _ ht
    exact ⟨T', i₁.le.trans hT, hxT', resM F i₁.le t,
      (app_resM φ _ t).trans (e.trans (resM_resM hT i₂.le s))⟩
  choose T hT hx t ht using H
  refine fun_ext_of_cover T hT (fun x hxW => Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hx _⟩) fun x => ?_
  rw [← dualApp_resM, ← ht, ← dualApp_dualMap, hl]
  exact (map_zero _).symm

variable (F) in

def cartierDualToBidual : F ⟶ dual (dual F) :=
  homOfLinear (fun V =>
    { toFun s := dualMk (fun W h =>
        { toFun l := dualApp l le_rfl (resM F h s)
          map_add' := fun _ _ => rfl
          map_smul' := fun a l => by
            rw [dualApp_smul, resG_self]; rfl })
        fun W W' h h' l => by
          change dualApp l h' (resM F _ s) = resG X h' (dualApp l le_rfl (resM F h s))
          rw [← dualApp_resM, resM_resM]
      map_add' := fun s t => dual_ext fun W h l => by
        change dualApp l le_rfl (resM F h (s + t)) = _
        rw [map_add, map_add]; rfl
      map_smul' := fun a s => dual_ext fun W h l => by
        change dualApp l le_rfl (resM F h (a • s)) = _
        rw [resM_smul, map_smul]; rfl })
    fun h s => dual_ext fun W h' l => congrArg (dualApp l le_rfl) (resM_resM h h' s)

@[simp] theorem dualSheafSectionApply_toBidual (s : Γ(F, V)) (h : W ≤ V) (l : Γ(dual F, W)) :
    dualApp ((cartierDualToBidual F).app V s) h l = dualApp l le_rfl (resM F h s) := rfl

@[reassoc] theorem toBidual_naturality_dualSheafTranspose (φ : F ⟶ G) :
    φ ≫ cartierDualToBidual G = cartierDualToBidual F ≫ dualMap (dualMap φ) := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s W h l
  first
  | simp [dualSheafSectionApply_toBidual, dualApp_dualMap, app_resM]
  | (simp only [Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, dualSheafSectionApply_toBidual, dualApp_dualMap, app_resM])

namespace IsFrame

variable {e : ι → Γ(F, U)}

def coord (he : IsFrame e) (i : ι) : Γ(dual F, U) :=
  dualMk (fun _ h => (he.basis h).coord i) fun _ _ h h' s => he.repr_resM h h' s i

@[simp] theorem dualApp_coord (he : IsFrame e) (i : ι) (h : V ≤ U) (s : Γ(F, V)) :
    dualApp (he.coord i) h s = (he.basis h).repr s i := rfl

theorem dualApp_coord_frame [DecidableEq ι] (he : IsFrame e) (i j : ι) (h : V ≤ U) :
    dualApp (he.coord i) h (resM F h (e j)) = if j = i then 1 else 0 := by
  rw [he.dualApp_coord, ← he.basis_apply h j, Module.Basis.repr_self, Finsupp.single_apply]

theorem dual_ext (he : IsFrame e) (h : V ≤ U) {l l' : Γ(dual F, V)}
    (H : ∀ i, dualApp l le_rfl (resM F h (e i)) = dualApp l' le_rfl (resM F h (e i))) : l = l' := by
  refine VB.dual_ext fun W h' s => ?_
  have key : ∀ m : Γ(VB.dual F, V), dualApp m h' s =
      ∑ i, (he.basis (h'.trans h)).repr s i * resG X h' (dualApp m le_rfl (resM F h (e i))) := by
    intro m
    conv_lhs => rw [← (he.basis (h'.trans h)).sum_repr s]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, he.basis_apply, ← dualApp_resM m le_rfl h', resM_resM, smul_eq_mul]
  rw [key l, key l']
  simp only [H]

private theorem dualApp_sum_smul_coord_eq (he : IsFrame e) (h : V ≤ U) (c : ι → Γ(X, V)) (j : ι) :
    dualApp (∑ i, c i • resM (VB.dual F) h (he.coord i)) le_rfl (resM F h (e j)) = c j := by
  classical
  rw [dualApp_sum, LinearMap.sum_apply]
  simp only [dualApp_smul, resG_self, dualApp_res, LinearMap.smul_apply, smul_eq_mul,
    he.dualApp_coord_frame]
  simp

theorem dual (he : IsFrame e) : IsFrame he.coord := by
  intro V h
  constructor
  · intro c c' hcc
    funext j
    have hj := congrArg (fun l => dualApp l le_rfl (resM F h (e j))) hcc
    simp only [Fintype.linearCombination_apply, dualApp_sum_smul_coord_eq] at hj
    exact hj
  · intro l
    refine ⟨fun i => dualApp l le_rfl (resM F h (e i)), ?_⟩
    rw [Fintype.linearCombination_apply]
    exact he.dual_ext h fun j => by rw [dualApp_sum_smul_coord_eq]

theorem dual_basis_repr (he : IsFrame e) (h : V ≤ U) (l : Γ(VB.dual F, V)) (i : ι) :
    (he.dual.basis h).repr l i = dualApp l le_rfl (resM F h (e i)) := by
  have h1 := he.dual.basis_equivFun_symm h ((he.dual.basis h).equivFun l)
  rw [LinearEquiv.symm_apply_apply] at h1
  conv_rhs => rw [h1]
  rw [dualApp_sum_smul_coord_eq, Module.Basis.equivFun_apply]

theorem toBidual_app (he : IsFrame e) (i : ι) : (cartierDualToBidual F).app U (e i) = he.dual.coord i := by
  classical
  refine he.dual.dual_ext le_rfl fun j => ?_
  rw [he.dual.dualApp_coord_frame i j le_rfl, dualSheafSectionApply_toBidual, dualApp_res, he.dualApp_coord_frame j i]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

end IsFrame

variable {r : ℕ}

theorem IsVB.dual (h : IsVB F r) : IsVB (dual F) r := by
  intro x
  obtain ⟨U, e, hx, he⟩ := h x
  exact ⟨U, he.coord, hx, he.dual⟩

theorem isIso_of_frames (φ : F ⟶ G) (h : ∀ x : X, ∃ (U : X.Opens) (e : ι → Γ(F, U)), x ∈ U ∧
    IsFrame e ∧ IsFrame fun i => φ.app U (e i)) : IsIso φ := by
  have hb : ∀ x : X, Function.Bijective (QCoh.stalkLinear φ x) := by
    intro x
    obtain ⟨U, e, hx, he, he'⟩ := h x
    have key : QCoh.stalkLinear φ x =
        ((he.stalkBasis x hx).equiv (he'.stalkBasis x hx) (Equiv.refl ι)).toLinearMap := by
      refine (he.stalkBasis x hx).ext fun i => ?_
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, IsFrame.stalkBasis_apply,
        IsFrame.stalkBasis_apply, QCoh.stalkLinear_germ]
    rw [key]
    exact LinearEquiv.bijective _
  have : Mono φ := (QCoh.mono_iff_stalkLinear_injective φ).2 fun x => (hb x).1
  have : Epi φ := (QCoh.epi_iff_stalkLinear_surjective φ).2 fun x => (hb x).2
  exact isIso_of_mono_of_epi φ

theorem IsVB.isIso_toBidual_of_local_frames (h : IsVB F r) : IsIso (cartierDualToBidual F) := by
  refine isIso_of_frames (ι := Fin r) _ fun x => ?_
  obtain ⟨U, e, hx, he⟩ := h x
  refine ⟨U, e, hx, he, ?_⟩
  simp only [he.toBidual_app]
  exact he.dual.dual

variable (X) in

def dualFreeIso (ι : Type) [Fintype ι] : freeModule X ι ≅ dual (freeModule X ι) :=
  (isFrame_freeFrame X ι).iso (isFrame_freeFrame X ι).dual

namespace IsFrame

variable [DecidableEq ι] {U' U'' : X.Opens} {e : ι → Γ(F, U)} {e' : ι → Γ(F, U')}
  {e'' : ι → Γ(F, U'')}

theorem resG_det (he : IsFrame e) (h : V ≤ U) (h' : W ≤ V) (s : ι → Γ(F, V)) :
    resG X h' ((he.basis h).det s) = (he.basis (h'.trans h)).det fun i => resM F h' (s i) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply]
  exact (he.repr_resM h h' (s j) i).symm

def detUnit (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) (h' : V ≤ U') : Γ(X, V)ˣ where
  val := (he.basis h).det (he'.basis h')
  inv := (he'.basis h').det (he.basis h)
  val_inv := by rw [Module.Basis.det_mul_det, Module.Basis.det_self]
  inv_val := by rw [Module.Basis.det_mul_det, Module.Basis.det_self]

theorem val_detUnit (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) (h' : V ≤ U') :
    (he.detUnit he' h h' : Γ(X, V)) = (he.basis h).det fun i => resM F h' (e' i) := by
  show (he.basis h).det (he'.basis h') = _
  rw [he'.coe_basis h']

theorem res_detUnit (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) (h' : V ≤ U') (hW : W ≤ V) :
    Semi.res hW (he.detUnit he' h h') = he.detUnit he' (hW.trans h) (hW.trans h') := by
  apply Units.ext
  rw [val_res, val_detUnit, val_detUnit, resG_det]
  simp only [resM_resM]

theorem detUnit_res (he : IsFrame e) (he' : IsFrame e') {T T' : X.Opens} (hT : T ≤ U)
    (hT' : T' ≤ U') (h : V ≤ T) (h' : V ≤ T') :
    (he.res hT).detUnit (he'.res hT') h h' = he.detUnit he' (h.trans hT) (h'.trans hT') := by
  have hb : (he.res hT).basis h = he.basis (h.trans hT) :=
    Module.Basis.eq_of_apply_eq fun i => by simp only [IsFrame.basis_apply, resM_resM]
  apply Units.ext
  rw [val_detUnit, val_detUnit, hb]
  simp only [resM_resM]

theorem detUnit_self (he : IsFrame e) (h h' : V ≤ U) : he.detUnit he h h' = 1 := by
  exact Units.ext (Module.Basis.det_self (he.basis h))

theorem detUnit_mul (he : IsFrame e) (he' : IsFrame e') (he'' : IsFrame e'') (h : V ≤ U)
    (h' : V ≤ U') (h'' : V ≤ U'') :
    he.detUnit he' h h' * he'.detUnit he'' h' h'' = he.detUnit he'' h h'' := by
  exact Units.ext (Module.Basis.det_mul_det (he.basis h) (he'.basis h') (he''.basis h''))

theorem det_eq_detUnit_mul (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) (h' : V ≤ U')
    (s : ι → Γ(F, V)) :
    (he.basis h).det s = he.detUnit he' h h' * (he'.basis h').det s := by
  show (he.basis h).det s = (he.basis h).det (he'.basis h') * (he'.basis h').det s
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
    Module.Basis.toMatrix_mul_toMatrix]

theorem detUnit_dual (he : IsFrame e) (he' : IsFrame e') (h : V ≤ U) (h' : V ≤ U') :
    he.dual.detUnit he'.dual h h' = (he.detUnit he' h h')⁻¹ := by
  apply Units.ext
  show (he.dual.basis h).det (he'.dual.basis h') = (he'.basis h').det (he.basis h)
  rw [Module.Basis.det_apply, Module.Basis.det_apply,
    ← Matrix.det_transpose (Module.Basis.toMatrix (he'.basis h') (he.basis h))]
  congr 1
  ext i j
  rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, dual_basis_repr he h,
    IsFrame.basis_apply, IsFrame.basis_apply, dualApp_res, dualApp_coord]

private theorem repr_map_iso_app_eq_repr (he : IsFrame e) (φ : F ⟶ G) [IsIso φ] (h : V ≤ U)
    (s : Γ(F, V)) (i : ι) :
    ((he.map_iso φ).basis h).repr (φ.app V s) i = (he.basis h).repr s i := by
  have key : φ.app V s = ∑ j, (he.basis h).repr s j • ((he.map_iso φ).basis h) j := by
    conv_lhs => rw [← (he.basis h).sum_repr s]
    rw [← appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, appLinear_apply]
    simp only [IsFrame.basis_apply, app_resM]
  rw [key, Module.Basis.repr_sum_self]

theorem detUnit_map_iso (he : IsFrame e) (he' : IsFrame e') (φ : F ⟶ G) [IsIso φ] (h : V ≤ U)
    (h' : V ≤ U') : (he.map_iso φ).detUnit (he'.map_iso φ) h h' = he.detUnit he' h h' := by
  apply Units.ext
  rw [val_detUnit, val_detUnit, Module.Basis.det_apply, Module.Basis.det_apply]
  congr 1
  ext i j
  simp only [Module.Basis.toMatrix_apply, ← app_resM]
  exact repr_map_iso_app_eq_repr he φ h _ i

private theorem pullbackSections_resM [F.IsQuasicoherent] (f : Y ⟶ X) (h : V ≤ U) {T : Y.Opens}
    (hT : T ≤ f ⁻¹ᵁ V) (x : Γ(F, U)) :
    QCoh.pullbackSections f F hT (resM F h x) =
      resM _ (hT.trans (f.preimage_mono h)) (QCoh.pullbackSections f F (le_refl (f ⁻¹ᵁ U)) x) := by
  rw [QCoh.pullbackSections_res f F hT h x,
    QCoh.res_pullbackSections f F (le_refl (f ⁻¹ᵁ U)) (hT.trans (f.preimage_mono h)) x]

omit [DecidableEq ι] in

theorem pullback_basis_repr [F.IsQuasicoherent] (he : IsFrame e) (f : Y ⟶ X) (h : V ≤ U)
    {T : Y.Opens} (hT : T ≤ f ⁻¹ᵁ V) (s : Γ(F, V)) (i : ι) :
    ((he.pullback f).basis (hT.trans (f.preimage_mono h))).repr
      (QCoh.pullbackSections f F hT s) i = f.appLE V T hT ((he.basis h).repr s i) := by
  have key : QCoh.pullbackSections f F hT s = ∑ j, f.appLE V T hT ((he.basis h).repr s j) •
      ((he.pullback f).basis (hT.trans (f.preimage_mono h))) j := by
    conv_lhs => rw [← (he.basis h).sum_repr s]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [QCoh.pullbackSections_smul, IsFrame.basis_apply, IsFrame.basis_apply, pullbackSections_resM]
  rw [key, Module.Basis.repr_sum_self]

theorem val_detUnit_pullback [F.IsQuasicoherent] (he : IsFrame e) (he' : IsFrame e') (f : Y ⟶ X)
    (h : V ≤ U) (h' : V ≤ U') {T : Y.Opens} (hT : T ≤ f ⁻¹ᵁ V) :
    (((he.pullback f).detUnit (he'.pullback f) (hT.trans (f.preimage_mono h))
      (hT.trans (f.preimage_mono h')) : Γ(Y, T)ˣ) : Γ(Y, T)) =
        (f.appLE V T hT).hom (he.detUnit he' h h' : Γ(X, V)) := by
  rw [val_detUnit, val_detUnit, Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply]
  rw [← pullbackSections_resM f h' hT (e' j), pullback_basis_repr he f h hT]
  try rfl

end IsFrame

variable (F r) in

structure Chart where

  U : X.Opens

  e : Fin r → Γ(F, U)

  isFrame : IsFrame e

variable (F r) in

def det : LB X where
  ι := Chart F r
  U c := c.U
  g c c' := c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right

theorem isLB_det_iff : (det F r).IsLB ↔ IsVB F r := by
  constructor
  · intro hL x
    have hx : x ∈ (⨆ c, (det F r).U c) := by rw [hL.1]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨c.U, c.e, hc, c.isFrame⟩
  · intro h
    refine LB.IsLB.mk ?_ ?_ ?_
    · rw [eq_top_iff]
      intro x _
      obtain ⟨U, e, hx, he⟩ := h x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, e, he⟩, hx⟩
    · intro c
      exact (IsFrame.res_detUnit _ _ _ _ _).trans (IsFrame.detUnit_self _ _ _)
    · intro i j k
      exact (congrArg₂ (· * ·) (IsFrame.res_detUnit _ _ _ _ _) (IsFrame.res_detUnit _ _ _ _ _)).trans
        ((IsFrame.detUnit_mul _ _ _ _ _ _).trans (IsFrame.res_detUnit _ _ _ _ _).symm)

theorem IsVB.isLB_det (h : IsVB F r) : (det F r).IsLB := isLB_det_iff.2 h

def wedgeFun (s : Fin r → Γ(F, V)) : Γ(toMod (det F r), V) :=
  LB.mkSec (fun c : Chart F r =>
      (c.isFrame.basis (inf_le_right : V ⊓ c.U ≤ c.U)).det fun i => resM F inf_le_left (s i))
    fun c c' => by
      refine (c.isFrame.resG_det _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·)
        (congrArg Units.val (IsFrame.res_detUnit _ _ _ _ _)) (c'.isFrame.resG_det _ _ _)).symm)
      exact (c.isFrame.det_eq_detUnit_mul c'.isFrame _ inf_le_right _).trans
        (congrArg _ (congrArg _ (funext fun i => (resM_resM _ _ _).trans (resM_resM _ _ _).symm)))

def detCoord (t : Γ(toMod (det F r), V)) (c : Chart F r) : Γ(X, V ⊓ c.U) := LB.coord t c

theorem det_sec_ext {t t' : Γ(toMod (det F r), V)} (h : ∀ c, detCoord t c = detCoord t' c) :
    t = t' := LB.sec_ext h

@[simp] theorem detCoord_add (t t' : Γ(toMod (det F r), V)) (c : Chart F r) :
    detCoord (t + t') c = detCoord t c + detCoord t' c := rfl

@[simp] theorem detCoord_smul (a : Γ(X, V)) (t : Γ(toMod (det F r), V)) (c : Chart F r) :
    detCoord (a • t) c = resG X inf_le_left a * detCoord t c := rfl

@[simp] theorem detCoord_zero (c : Chart F r) : detCoord (0 : Γ(toMod (det F r), V)) c = 0 := rfl

theorem detCoord_wedgeFun (s : Fin r → Γ(F, V)) (c : Chart F r) :
    detCoord (wedgeFun s) c =
      (c.isFrame.basis (inf_le_right : V ⊓ c.U ≤ c.U)).det fun i => resM F inf_le_left (s i) := rfl

variable (F r V) in

def wedge : Γ(F, V) [⋀^Fin r]→ₗ[Γ(X, V)] Γ(toMod (det F r), V) where
  toFun := wedgeFun
  map_update_add' s j a b := det_sec_ext fun c => by
    simp only [detCoord_add, detCoord_wedgeFun,
      Function.apply_update (fun _ => resM F (inf_le_left : V ⊓ c.U ≤ V)) s j,
      map_add, AlternatingMap.map_update_add]
  map_update_smul' s j a b := det_sec_ext fun c => by
    simp only [detCoord_smul, detCoord_wedgeFun,
      Function.apply_update (fun _ => resM F (inf_le_left : V ⊓ c.U ≤ V)) s j,
      resM_smul, AlternatingMap.map_update_smul, smul_eq_mul]
  map_eq_zero_of_eq' s i j e hij := det_sec_ext fun c => by
    rw [detCoord_wedgeFun, detCoord_zero]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (congrArg (resM F inf_le_left) e) hij

theorem detCoord_wedge (s : Fin r → Γ(F, V)) (c : Chart F r) :
    detCoord (wedge F V r s) c =
      (c.isFrame.basis (inf_le_right : V ⊓ c.U ≤ c.U)).det fun i => resM F inf_le_left (s i) := rfl

theorem resM_wedge (h : W ≤ V) (s : Fin r → Γ(F, V)) :
    resM _ h (wedge F V r s) = wedge F W r fun i => resM F h (s i) := by
  refine det_sec_ext fun c => ?_
  rw [detCoord_wedge (V := W)]
  have e : detCoord (resM (toMod (det F r)) h (wedge F V r s)) c =
      resG X (inf_le_inf_right c.U h) (detCoord (wedge F V r s) c) := rfl
  rw [e, detCoord_wedge, IsFrame.resG_det]
  simp only [resM_resM]

theorem wedge_frame (h : IsVB F r) (c : Chart F r) :
    wedge F c.U r c.e = LB.chartSec h.isLB_det c := by
  refine det_sec_ext fun c' => ?_
  rw [detCoord_wedge]
  refine Eq.trans ?_ (LB.coord_chartSec (L := det F r) h.isLB_det c c').symm
  refine Eq.trans ?_ (congrArg (resG X _) (IsFrame.val_detUnit c'.isFrame c.isFrame inf_le_left inf_le_right)).symm
  refine Eq.trans ?_ (IsFrame.resG_det c'.isFrame _ _ _).symm
  congr 1
  funext i
  exact (resM_resM _ _ (c.e i)).symm

theorem IsFrame.wedge (h : IsVB F r) {e : Fin r → Γ(F, U)} (he : IsFrame e) :
    IsFrame fun _ : Fin 1 => wedge F U r e := by
  have H := isFrame_chartSec h.isLB_det (⟨U, e, he⟩ : Chart F r)
  rw [← wedge_frame h (⟨U, e, he⟩ : Chart F r)] at H
  exact H

theorem lbIso_det_of_frames {L : LB X} (hL : L.IsLB) (e : ∀ i, Fin r → Γ(F, L.U i))
    (he : ∀ i, IsFrame (e i))
    (hg : ∀ i j, L.g i j = (he i).detUnit (he j) inf_le_left inf_le_right) :
    IsVB F r ∧ LBIso L (det F r) := by
  have hVB : IsVB F r := fun x => by
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨L.U i, e i, hi, he i⟩
  refine ⟨hVB, CechPic.iso_of_chart hVB.isLB_det ⟨fun i => ⟨L.U i, e i, he i⟩, ?_, ?_⟩⟩
  · intro i
    exact fun x hx => hx
  · intro y i j _ _
    rw [hg i j]
    rfl

theorem IsVB.lbIso_det_of_iso (h : IsVB F r) (φ : F ≅ G) : LBIso (det F r) (det G r) := (lbIso_det_of_frames h.isLB_det _ (fun c => c.isFrame.map_iso φ.hom)
    (fun _ _ => (IsFrame.detUnit_map_iso _ _ _ _ _).symm)).2

theorem IsVB.lbIso_det_dual (h : IsVB F r) : LBIso (CechPic.dual (det F r)) (det (VB.dual F) r) := (lbIso_det_of_frames (CechPic.isLB_dual h.isLB_det) _ (fun c => c.isFrame.dual)
    (fun _ _ => (IsFrame.detUnit_dual _ _ _ _).symm)).2

theorem IsVB.lbIso_det_pullback (h : IsVB F r) (f : Y ⟶ X) :
    LBIso ((det F r).pull f) (det ((Scheme.Modules.pullback f).obj F) r) := by
  have hle : ∀ j : ((det F r).pull f).ι, ((det F r).pull f).U j ≤ f ⁻¹ᵁ (j PUnit.unit).U :=
    fun j y hy => Set.mem_iInter.1 hy PUnit.unit
  have hpg : ∀ (j j' : ((det F r).pull f).ι)
      (hh : ((det F r).pull f).U j ⊓ ((det F r).pull f).U j' ≤
        f ⁻¹ᵁ ((j PUnit.unit).U ⊓ (j' PUnit.unit).U)),
      (((det F r).pull f).g j j' : Γ(Y, ((det F r).pull f).U j ⊓ ((det F r).pull f).U j')) =
        (f.appLE _ _ hh).hom
          ((j PUnit.unit).isFrame.detUnit (j' PUnit.unit).isFrame inf_le_left inf_le_right :
            Γ(X, (j PUnit.unit).U ⊓ (j' PUnit.unit).U)) := by
    intro j j' hh
    unfold LB.pull
    unfold LB.LinComb
    dsimp only
    rw [Fintype.prod_unique]
    simp only [zpow_one]
    rfl
  have := h.isQuasicoherent
  have hL : ((det F r).pull f).IsLB := LB.isLB_pull h.isLB_det f
  refine (lbIso_det_of_frames hL
    (fun j i => resM ((Scheme.Modules.pullback f).obj F) (hle j)
      (QCoh.pullbackSections f F (le_refl (f ⁻¹ᵁ (j PUnit.unit).U)) ((j PUnit.unit).e i)))
    (fun j => ((j PUnit.unit).isFrame.pullback f).res (hle j)) fun j j' => ?_).2
  have hh : ((det F r).pull f).U j ⊓ ((det F r).pull f).U j' ≤
      f ⁻¹ᵁ ((j PUnit.unit).U ⊓ (j' PUnit.unit).U) :=
    fun y hy => ⟨hle j hy.1, hle j' hy.2⟩
  refine Units.ext ?_
  rw [hpg j j' hh,
    IsFrame.detUnit_res ((j PUnit.unit).isFrame.pullback f) ((j' PUnit.unit).isFrame.pullback f),
    IsFrame.val_detUnit_pullback (j PUnit.unit).isFrame (j' PUnit.unit).isFrame f inf_le_left inf_le_right hh]

theorem lbIso_det_toMod {L : LB X} (hL : L.IsLB) : LBIso L (det (toMod L) 1) := by
  refine (lbIso_det_of_frames hL (fun i _ => LB.chartSec hL i) (fun i => isFrame_chartSec hL i)
    (fun i j => ?_)).2
  have key : resM (toMod L) (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (LB.chartSec hL j) =
      ((L.g i j : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) •
        resM (toMod L) (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (LB.chartSec hL i) := by
    refine LB.sec_ext fun k => ?_
    rw [LB.coord_smul]
    change resG X _ (LB.coord (LB.chartSec hL j) k) =
      resG X _ ((L.g i j : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) * resG X _ (LB.coord (LB.chartSec hL i) k)
    rw [LB.coord_chartSec, LB.coord_chartSec, resG_resG, resG_resG]
    have c0 := congrArg Units.val (hL.3 k i j)
    have c := congrArg (resG X (show (L.U i ⊓ L.U j) ⊓ L.U k ≤ _ by
      intro x hx
      simp only [TopologicalSpace.Opens.mem_inf] at hx ⊢
      tauto)) c0
    simp only [Units.val_mul, map_mul, val_res, resG_resG] at c
    rw [mul_comm]
    exact c.symm
  refine Units.ext ?_
  rw [IsFrame.val_detUnit]
  simp only [Module.Basis.det_apply, Matrix.det_unique, Module.Basis.toMatrix_apply]
  rw [key, map_smul, ← IsFrame.basis_apply (isFrame_chartSec hL i) inf_le_left (default : Fin 1),
    Module.Basis.repr_self]
  simp

def IsVB.isoDet (h : IsVB F 1) : F ≅ toMod (det F 1) :=
  let φ : F ⟶ toMod (det F 1) := homOfLinear
    (fun V => (AlternatingMap.ofSubsingleton _ _ _ (0 : Fin 1)).symm (wedge F V 1))
    fun hW s => (resM_wedge hW fun _ => s).symm
  haveI : IsIso φ := isIso_of_frames _ fun x =>
    have ⟨U, e, hx, he⟩ := h x
    ⟨U, e, hx, he, by
      have (i : Fin 1) : φ.app U (e i) = wedge F U 1 e :=
        congrArg (wedge F U 1) (funext fun j => congrArg e (Subsingleton.elim _ _))
      rw [funext this]
      exact he.wedge h⟩
  asIso φ

theorem IsFrame.cls_det_eq_zero {e : Fin r → Γ(F, ⊤)} (he : IsFrame e) (h : (det F r).IsLB) :
    CechPic.cls _ h = 0 := by
  have H := (lbIso_det_of_frames (LB.isLB_triv X) (fun _ => e) (fun _ => he)
    (fun _ _ => (IsFrame.detUnit_self he _ _).symm)).2
  exact ((CechPic.cls_eq_iff (LB.isLB_triv X) h).2 H).symm.trans rfl

example {e : Fin 2 → Γ(F, U)} (he : IsFrame e) :
    (he.detUnit (he.comp_equiv (Equiv.swap 0 1)) le_rfl le_rfl : Γ(X, U)) = -1 := by
  rw [IsFrame.val_detUnit]
  have := (he.basis le_rfl).det.map_swap (he.basis le_rfl) (i := 0) (j := 1) (by decide)
  rw [Module.Basis.det_self, he.coe_basis] at this
  exact this

end GlobalTheory.VB
