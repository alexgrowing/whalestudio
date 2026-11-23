import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open GlobalTheory.LB (resG_resG resG_self homOfLinear)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.DualPull

variable {X Y : Scheme.{0}}

abbrev cutO (T W : Y.Opens) : Y.Opens := T.ι ''ᵁ T.ι ⁻¹ᵁ W

theorem cutO_le (T W : Y.Opens) : cutO T W ≤ W := T.ι.image_preimage_le W

theorem cutO_le' (T W : Y.Opens) : cutO T W ≤ T := T.ι_image_le _

theorem le_cutO {T W S : Y.Opens} (h : S ≤ T) (h' : S ≤ W) : S ≤ cutO T W := by
  rw [cutO, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact le_inf h h'

theorem cutO_mono (T : Y.Opens) {W W' : Y.Opens} (h : W' ≤ W) : cutO T W' ≤ cutO T W :=
  le_cutO (cutO_le' _ _) ((cutO_le _ _).trans h)

def cut (T : Y.Opens) : Y.Modules :=
  (Scheme.Modules.pushforward T.ι).obj ((structureModule Y).restrict T.ι)

def cutEquiv (T W : Y.Opens) : Γ(cut T, W) ≃+ Γ(Y, cutO T W) := AddEquiv.refl _

theorem cutEquiv_smul (T W : Y.Opens) (a : Γ(Y, W)) (s : Γ(cut T, W)) :
    cutEquiv T W (a • s) = resG Y (cutO_le T W) a * cutEquiv T W s :=
  congrArg (· * cutEquiv T W s) congr($(T.ι.app_appIso_inv W) a)

theorem cutEquiv_res (T : Y.Opens) {W W' : Y.Opens} (h : W' ≤ W) (s : Γ(cut T, W)) :
    cutEquiv T W' (resM (cut T) h s) = resG Y (cutO_mono T h) (cutEquiv T W s) := rfl

variable {P : Y.Modules} {T : Y.Opens}

def toCut (l : Γ(dual P, T)) : P ⟶ cut T :=
  homOfLinear (fun W =>
    { toFun s := (cutEquiv T W).symm (dualApp l (cutO_le' T W) (resM P (cutO_le T W) s))
      map_add' s t := by simp only [map_add]
      map_smul' a s := (cutEquiv T W).injective (by
        rw [RingHom.id_apply, cutEquiv_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          resM_smul, map_smul, smul_eq_mul]) })
    fun {W W'} h s => (cutEquiv T W').injective (by
      change dualApp l _ (resM P _ (resM P h s)) = resG Y (cutO_mono T h) (dualApp l _ (resM P _ s))
      rw [← dualApp_resM, resM_resM, resM_resM])

theorem toCut_app (l : Γ(dual P, T)) (W : Y.Opens) (s : Γ(P, W)) :
    cutEquiv T W ((toCut l).app W s) = dualApp l (cutO_le' T W) (resM P (cutO_le T W) s) := rfl

theorem toCut_injective {l l' : Γ(dual P, T)} (h : toCut l = toCut l') : l = l' :=
  dual_ext fun W hW s => by
    have := congrArg (resG Y (le_cutO hW le_rfl)) ((toCut_app l W s).symm.trans (h ▸ toCut_app l' W s))
    rwa [← dualApp_resM, ← dualApp_resM, resM_resM, resM_self] at this

def ofCut (φ : P ⟶ cut T) : Γ(dual P, T) :=
  dualMk (fun W h =>
    { toFun s := resG Y (le_cutO h le_rfl) (cutEquiv T W (φ.app W s))
      map_add' s t := by simp only [map_add]
      map_smul' a s := by
        rw [Scheme.Modules.Hom.app_smul, cutEquiv_smul, map_mul, resG_resG, resG_self]; rfl })
    fun W W' h h' s => by
      change resG Y _ (cutEquiv T W' (φ.app W' (resM P h' s))) = resG Y h' (resG Y _ _)
      rw [app_resM, cutEquiv_res, resG_resG, resG_resG]

theorem dualApp_ofCut (φ : P ⟶ cut T) {W : Y.Opens} (h : W ≤ T) (s : Γ(P, W)) :
    dualApp (ofCut φ) h s = resG Y (le_cutO h le_rfl) (cutEquiv T W (φ.app W s)) := rfl

variable (f : Y ⟶ X)

def adj {F : X.Modules} {G : Y.Modules} (ψ : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    (Scheme.Modules.pullback f).obj F ⟶ G :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).symm ψ

theorem adj_app {F : X.Modules} {G : Y.Modules} (ψ : F ⟶ (Scheme.Modules.pushforward f).obj G)
    {V : X.Opens} (e : T ≤ f ⁻¹ᵁ V) (s : Γ(F, V)) :
    (adj f ψ).app T (pullbackSections f F e s) = resM G e (ψ.app V s) := by
  refine (QCoh.hom_app_res (adj f ψ) e _).trans (congrArg (resM G e) ?_)
  have := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).apply_symm_apply ψ
  rw [Adjunction.homEquiv_unit] at this
  exact congr(($this).app V s)

theorem pull_ext {F : X.Modules} {G : Y.Modules} {φ φ' : (Scheme.Modules.pullback f).obj F ⟶ G}
    (h : ∀ (V : X.Opens) (s : Γ(F, V)), φ.app _ (pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s) =
      φ'.app _ (pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s)) : φ = φ' := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F G).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  have e : pullbackSections f F (le_refl (f ⁻¹ᵁ V)) s = _ := QCoh.res_self _ _ _
  exact (congrArg (φ.app _) e).symm.trans ((h V s).trans (congrArg (φ'.app _) e))

variable {F G : X.Modules} {V : X.Opens}

theorem dual_pull_ext (e : T ≤ f ⁻¹ᵁ V) {l l' : Γ(dual ((Scheme.Modules.pullback f).obj F), T)}
    (h : ∀ (W : X.Opens) (_ : W ≤ V) (S : Y.Opens) (hS : S ≤ T) (e' : S ≤ f ⁻¹ᵁ W) (s : Γ(F, W)),
      dualApp l hS (pullbackSections f F e' s) = dualApp l' hS (pullbackSections f F e' s)) :
    l = l' := by
  refine toCut_injective (pull_ext f fun W s => (cutEquiv T _).injective ?_)
  have e' : cutO T (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) :=
    le_inf (cutO_le T (f ⁻¹ᵁ W)) ((cutO_le' T (f ⁻¹ᵁ W)).trans e)
  have : resM _ (cutO_le T (f ⁻¹ᵁ W)) (pullbackSections f F (le_refl (f ⁻¹ᵁ W)) s) =
      pullbackSections f F e' (resM F inf_le_left s) :=
    (QCoh.res_pullbackSections f F _ _ _).trans (QCoh.pullbackSections_res f F e' _ _).symm
  rw [toCut_app, toCut_app, this]
  exact h _ inf_le_right _ _ _ _

theorem cutO_le_inf (V W : X.Opens) : cutO (f ⁻¹ᵁ V) (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) :=
  le_inf (cutO_le (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)) (cutO_le' (f ⁻¹ᵁ V) (f ⁻¹ᵁ W))

theorem appLE_resG {W : X.Opens} (h : W ≤ V) (e : T ≤ f ⁻¹ᵁ W) (a : Γ(X, V)) :
    f.appLE W T e (resG X h a) = f.appLE V T (e.trans (f.preimage_mono h)) a :=
  congr($(f.map_appLE e (homOfLE h).op) a)

theorem resG_appLE {S : Y.Opens} (h : S ≤ T) (e : T ≤ f ⁻¹ᵁ V) (a : Γ(X, V)) :
    resG Y h (f.appLE V T e a) = f.appLE V S (h.trans e) a :=
  congr($(f.appLE_map e (homOfLE h).op) a)

def formPush (l : Γ(dual F, V)) : F ⟶ (Scheme.Modules.pushforward f).obj (cut (f ⁻¹ᵁ V)) :=
  homOfLinear (fun W =>
    { toFun s := (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)).symm (f.appLE (W ⊓ V) _ (cutO_le_inf f V W)
        (dualApp l inf_le_right (resM F inf_le_left s)))
      map_add' s t := by simp only [map_add]; rfl
      map_smul' a s := (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W)).injective (by
        refine Eq.trans ?_ (cutEquiv_smul _ _ (f.app W a) _).symm
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          resM_smul, map_smul, smul_eq_mul, map_mul, appLE_resG]
        rfl) })
    fun {W W'} h s => (cutEquiv (f ⁻¹ᵁ V) (f ⁻¹ᵁ W')).injective (by
      change f.appLE (W' ⊓ V) _ _ (dualApp l _ (resM F _ (resM F h s))) =
        resG Y (cutO_mono _ (f.preimage_mono h)) (f.appLE (W ⊓ V) _ _ (dualApp l _ (resM F _ s)))
      rw [resG_appLE, ← appLE_resG f (inf_le_inf_right V h) (cutO_le_inf f V W'), ← dualApp_resM,
        resM_resM, resM_resM])

def pullForm (l : Γ(dual F, V)) : Γ(dual ((Scheme.Modules.pullback f).obj F), f ⁻¹ᵁ V) :=
  ofCut (adj f (formPush f l))

theorem dualApp_pullForm (l : Γ(dual F, V)) {W : X.Opens} (h : W ≤ V) (hT : T ≤ f ⁻¹ᵁ V)
    (e : T ≤ f ⁻¹ᵁ W) (s : Γ(F, W)) :
    dualApp (pullForm f l) hT (pullbackSections f F e s) = f.appLE W T e (dualApp l h s) := by
  rw [pullForm, dualApp_ofCut, adj_app]
  change resG Y _ (resG Y (cutO_mono _ e) (f.appLE (W ⊓ V) _ (cutO_le_inf f V W)
    (dualApp l inf_le_right (resM F inf_le_left s)))) = _
  rw [resG_appLE, resG_appLE, dualApp_resM l h, appLE_resG]

variable (F) in

def pullFormHom :
    dual F ⟶ (Scheme.Modules.pushforward f).obj (dual ((Scheme.Modules.pullback f).obj F)) :=
  homOfLinear (fun V =>
    { toFun l := pullForm f l
      map_add' l l' := dual_pull_ext f le_rfl fun W h S hS e s => by
        change _ = dualApp (pullForm f l) hS _ + dualApp (pullForm f l') hS _
        rw [dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_add,
          LinearMap.add_apply, map_add]
      map_smul' a l := dual_pull_ext f le_rfl fun W h S hS e s => by
        change _ = resG Y hS (f.app V a) * dualApp (pullForm f l) hS _
        rw [dualApp_pullForm f _ h, dualApp_pullForm f _ h, dualApp_smul,
          LinearMap.smul_apply, smul_eq_mul, map_mul, appLE_resG]
        rfl })
    fun {V V'} hV l => dual_pull_ext f le_rfl fun W h S hS e s => by
      change dualApp (pullForm f (resM _ hV l)) hS _ =
        dualApp (pullForm f l) (hS.trans (f.preimage_mono hV)) _
      rw [dualApp_pullForm f _ h, dualApp_pullForm f _ (h.trans hV), dualApp_res]

variable (F) in

def theta : (Scheme.Modules.pullback f).obj (dual F) ⟶ dual ((Scheme.Modules.pullback f).obj F) :=
  adj f (pullFormHom f F)

theorem dualApp_theta (l : Γ(dual F, V)) {W : X.Opens} (h : W ≤ V) (e : T ≤ f ⁻¹ᵁ V)
    {S : Y.Opens} (hS : S ≤ T) (e' : S ≤ f ⁻¹ᵁ W) (s : Γ(F, W)) :
    dualApp ((theta f F).app T (pullbackSections f (dual F) e l)) hS (pullbackSections f F e' s) =
      f.appLE W S e' (dualApp l h s) := by
  rw [theta, adj_app]
  exact dualApp_pullForm f l h (hS.trans e) e' s

theorem theta_naturality (φ : F ⟶ G) :
    (Scheme.Modules.pullback f).map (dualMap φ) ≫ theta f F =
      theta f G ≫ dualMap ((Scheme.Modules.pullback f).map φ) :=
  pull_ext f fun V l => dual_pull_ext f le_rfl fun W h S hS e s => by
    change dualApp ((theta f F).app _ (((Scheme.Modules.pullback f).map (dualMap φ)).app _ _)) hS _ =
      dualApp ((theta f G).app _ _) hS (((Scheme.Modules.pullback f).map φ).app _ _)
    rw [QCoh.pullback_map_app_pullbackSections, QCoh.pullback_map_app_pullbackSections,
      dualApp_theta f _ h, dualApp_theta f _ h, dualApp_dualMap]

theorem isIso_theta {r : ℕ} (h : IsVB F r) : IsIso (theta f F) := by
  have := h.isQuasicoherent
  have := h.dual.isQuasicoherent
  refine isIso_of_frames (ι := Fin r) _ fun y => ?_
  obtain ⟨U, e, hx, he⟩ := h (f y)
  refine ⟨f ⁻¹ᵁ U, _, hx, he.dual.pullback f, ?_⟩
  have H (i : Fin r) : (theta f F).app _ (pullbackSections f (dual F) (le_refl (f ⁻¹ᵁ U))
      (he.coord i)) = (he.pullback f).coord i :=
    dual_pull_ext f le_rfl fun W hW S hS e' s => by
      rw [dualApp_theta f _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]
      exact (he.pullback_basis_repr f hW e' s i).symm
  rw [funext H]
  exact (he.pullback f).dual

theorem exists_dual_pullback : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X), ∃ θ : ∀ F : X.Modules, (Scheme.Modules.pullback f).obj (dual F) ⟶ dual ((Scheme.Modules.pullback f).obj F), (∀ (F G : X.Modules) (φ : F ⟶ G), (Scheme.Modules.pullback f).map (dualMap φ) ≫ θ F = θ G ≫ dualMap ((Scheme.Modules.pullback f).map φ)) ∧ (∀ (F : X.Modules) (V : X.Opens) (T : Y.Opens) (e : T ≤ f ⁻¹ᵁ V) (l : Γ(dual F, V)) (s : Γ(F, V)), dualApp ((θ F).app T (GlobalTheory.QCoh.pullbackSections f (dual F) e l)) le_rfl (GlobalTheory.QCoh.pullbackSections f F e s) = f.appLE V T e (dualApp l le_rfl s)) ∧ ∀ (F : X.Modules) (r : ℕ), IsVB F r → IsIso (θ F) :=
  fun _ _ f => ⟨theta f, fun _ _ φ => theta_naturality f φ,
    fun _ _ _ e l s => dualApp_theta f l le_rfl e le_rfl e s, fun _ _ h => isIso_theta f h⟩

end GlobalTheory.DualPull
