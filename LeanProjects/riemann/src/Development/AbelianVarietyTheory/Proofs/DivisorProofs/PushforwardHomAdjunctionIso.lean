import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

set_option autoImplicit false

noncomputable section

open GlobalTheory.LB (resG_resG resG_self homOfLinear)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (cutO cutO_le cutO_le' le_cutO cutO_mono cutO_le_inf adj adj_app pull_ext)

namespace GlobalTheory.HomPull

variable {X Y : Scheme.{0}}

def cutN (N : Y.Modules) (T : Y.Opens) : Y.Modules :=
  (Scheme.Modules.pushforward T.ι).obj (N.restrict T.ι)

def cutNEquiv (N : Y.Modules) (T S : Y.Opens) : Γ(cutN N T, S) ≃+ Γ(N, cutO T S) := AddEquiv.refl _

theorem cutNEquiv_smul (N : Y.Modules) (T S : Y.Opens) (a : Γ(Y, S)) (s : Γ(cutN N T, S)) :
    cutNEquiv N T S (a • s) = resG Y (cutO_le T S) a • cutNEquiv N T S s :=
  congrArg (· • cutNEquiv N T S s) congr($(T.ι.app_appIso_inv S) a)

theorem cutNEquiv_res (N : Y.Modules) (T : Y.Opens) {S S' : Y.Opens} (h : S' ≤ S)
    (s : Γ(cutN N T, S)) :
    cutNEquiv N T S' (resM (cutN N T) h s) = resM N (cutO_mono T h) (cutNEquiv N T S s) := rfl

variable {P N : Y.Modules} {T : Y.Opens}

def toCutN (l : Γ(homMod P N, T)) : P ⟶ cutN N T :=
  homOfLinear (fun S =>
    { toFun s := (cutNEquiv N T S).symm (homApp l (cutO_le' T S) (resM P (cutO_le T S) s))
      map_add' s t := by simp only [map_add]
      map_smul' a s := (cutNEquiv N T S).injective (by
        rw [RingHom.id_apply, cutNEquiv_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          resM_smul, map_smul]) })
    fun {S S'} h s => (cutNEquiv N T S').injective (by
      change homApp l _ (resM P _ (resM P h s)) = resM N (cutO_mono T h) (homApp l _ (resM P _ s))
      rw [← homApp_resM, resM_resM, resM_resM])

theorem toCutN_app (l : Γ(homMod P N, T)) (S : Y.Opens) (s : Γ(P, S)) :
    cutNEquiv N T S ((toCutN l).app S s) = homApp l (cutO_le' T S) (resM P (cutO_le T S) s) := rfl

theorem toCutN_injective {l l' : Γ(homMod P N, T)} (h : toCutN l = toCutN l') : l = l' :=
  hom_ext fun S hS s => by
    have := congrArg (resM N (le_cutO hS le_rfl))
      ((toCutN_app l S s).symm.trans (h ▸ toCutN_app l' S s))
    rwa [← homApp_resM, ← homApp_resM, resM_resM, resM_self] at this

def ofCutN (φ : P ⟶ cutN N T) : Γ(homMod P N, T) :=
  homMk (fun S h =>
    { toFun s := resM N (le_cutO h le_rfl) (cutNEquiv N T S (φ.app S s))
      map_add' s t := by simp only [map_add]
      map_smul' a s := by
        rw [Scheme.Modules.Hom.app_smul, cutNEquiv_smul, resM_smul, resG_resG, resG_self]; rfl })
    fun S S' h h' s => by
      change resM N _ (cutNEquiv N T S' (φ.app S' (resM P h' s))) = resM N h' (resM N _ _)
      rw [app_resM, cutNEquiv_res, resM_resM, resM_resM]

theorem homApp_ofCutN (φ : P ⟶ cutN N T) {S : Y.Opens} (h : S ≤ T) (s : Γ(P, S)) :
    homApp (ofCutN φ) h s = resM N (le_cutO h le_rfl) (cutNEquiv N T S (φ.app S s)) := rfl

variable (f : Y ⟶ X) {F : X.Modules} {V : X.Opens}

theorem hom_pull_ext (e : T ≤ f ⁻¹ᵁ V)
    {l l' : Γ(homMod ((Scheme.Modules.pullback f).obj F) N, T)}
    (h : ∀ (W : X.Opens) (_ : W ≤ V) (S : Y.Opens) (hS : S ≤ T) (e' : S ≤ f ⁻¹ᵁ W) (s : Γ(F, W)),
      homApp l hS (pullbackSections f F e' s) = homApp l' hS (pullbackSections f F e' s)) :
    l = l' := by
  refine toCutN_injective (pull_ext f fun W s => (cutNEquiv N T _).injective ?_)
  have e' : cutO T (f ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (W ⊓ V) :=
    le_inf (cutO_le T (f ⁻¹ᵁ W)) ((cutO_le' T (f ⁻¹ᵁ W)).trans e)
  have : resM _ (cutO_le T (f ⁻¹ᵁ W)) (pullbackSections f F (le_refl (f ⁻¹ᵁ W)) s) =
      pullbackSections f F e' (resM F inf_le_left s) :=
    (QCoh.res_pullbackSections f F _ _ _).trans (QCoh.pullbackSections_res f F e' _ _).symm
  rw [toCutN_app, toCutN_app, this]
  exact h _ inf_le_right _ _ _ _

end GlobalTheory.HomPull

namespace GlobalTheory.HomPull

variable {X Y : Scheme.{0}} (ρ : Y ⟶ X) (F : X.Modules) (N : Y.Modules)

theorem app_resG {W W' : X.Opens} (h : W' ≤ W) (a : Γ(X, W)) :
    ρ.app W' (resG X h a) = resG Y (ρ.preimage_mono h) (ρ.app W a) :=
  congr($(ρ.naturality (homOfLE h).op) a)

theorem appLE_self (W : X.Opens) (a : Γ(X, W)) : ρ.appLE W (ρ ⁻¹ᵁ W) le_rfl a = ρ.app W a :=
  by rw [Scheme.Hom.app_eq_appLE]

variable {F N} in

def fwdSec {V : X.Opens} (φ : Γ(homMod ((Scheme.Modules.pullback ρ).obj F) N, ρ ⁻¹ᵁ V)) :
    Γ(homMod F ((Scheme.Modules.pushforward ρ).obj N), V) :=
  homMk (fun V' h =>
    { toFun s := homApp φ (ρ.preimage_mono h) (pullbackSections ρ F le_rfl s)
      map_add' s t := (congrArg _ (map_add _ s t)).trans (map_add _ _ _)
      map_smul' a s := by
        rw [QCoh.pullbackSections_smul, map_smul, appLE_self]
        rfl })
    fun V' V'' h h' s => by
      change homApp φ _ (pullbackSections ρ F le_rfl (resM F h' s)) =
        resM N (ρ.preimage_mono h') (homApp φ _ (pullbackSections ρ F le_rfl s))
      rw [← homApp_resM, QCoh.pullbackSections_res]
      exact congrArg _ (QCoh.res_pullbackSections ρ F _ _ _).symm

theorem homApp_fwdSec {V : X.Opens} (φ : Γ(homMod ((Scheme.Modules.pullback ρ).obj F) N, ρ ⁻¹ᵁ V))
    {V' : X.Opens} (h : V' ≤ V) (s : Γ(F, V')) :
    homApp (fwdSec ρ φ) h s = homApp φ (ρ.preimage_mono h) (pullbackSections ρ F le_rfl s) := rfl

def fwdHom : (Scheme.Modules.pushforward ρ).obj (homMod ((Scheme.Modules.pullback ρ).obj F) N) ⟶
    homMod F ((Scheme.Modules.pushforward ρ).obj N) :=
  homOfLinear (fun V =>
    { toFun φ := fwdSec ρ φ
      map_add' φ φ' := hom_ext fun _ _ _ => rfl
      map_smul' a φ := hom_ext fun V' h s => by
        show homApp (ρ.app V a • (show Γ(homMod ((Scheme.Modules.pullback ρ).obj F) N, ρ ⁻¹ᵁ V) from φ))
          (ρ.preimage_mono h) _ = _
        rw [homApp_smul, RingHom.id_apply, homApp_smul]
        exact congrArg (fun b => b • homApp φ (ρ.preimage_mono h) (pullbackSections ρ F le_rfl s))
          (app_resG ρ h a).symm })
    fun _ _ => hom_ext fun _ _ _ => rfl

theorem fwdSec_injective (V : X.Opens) :
    Function.Injective (fwdSec ρ (F := F) (N := N) (V := V)) := fun φ φ' e =>
  hom_pull_ext ρ le_rfl fun W hW S hS e' s => by
    have := congrArg (resM N e') (congr(homApp $e hW s))
    rw [homApp_fwdSec, homApp_fwdSec, ← homApp_resM, ← homApp_resM] at this
    exact (congrArg (homApp φ hS) (QCoh.res_pullbackSections ρ F le_rfl e' s)).symm.trans
      (this.trans (congrArg (homApp φ' hS) (QCoh.res_pullbackSections ρ F le_rfl e' s)))

end GlobalTheory.HomPull

namespace GlobalTheory.HomPull

variable {X Y : Scheme.{0}} (ρ : Y ⟶ X) (F : X.Modules) (N : Y.Modules)

variable {F N} in

def pushVal {V W : X.Opens} (ψ : Γ(homMod F ((Scheme.Modules.pushforward ρ).obj N), V))
    (h : W ≤ V) (s : Γ(F, W)) : Γ(N, ρ ⁻¹ᵁ W) :=
  homApp ψ h s

variable {F N}

theorem pushVal_add {V W : X.Opens} (ψ : Γ(homMod F ((Scheme.Modules.pushforward ρ).obj N), V))
    (h : W ≤ V) (s t : Γ(F, W)) : pushVal ρ ψ h (s + t) = pushVal ρ ψ h s + pushVal ρ ψ h t :=
  map_add (homApp ψ h) s t

theorem pushVal_smul {V W : X.Opens} (ψ : Γ(homMod F ((Scheme.Modules.pushforward ρ).obj N), V))
    (h : W ≤ V) (a : Γ(X, W)) (s : Γ(F, W)) :
    pushVal ρ ψ h (a • s) = ρ.app W a • pushVal ρ ψ h s :=
  map_smul (homApp ψ h) a s

theorem pushVal_res {V W T : X.Opens} (ψ : Γ(homMod F ((Scheme.Modules.pushforward ρ).obj N), V))
    (h : W ≤ V) (h' : T ≤ W) (s : Γ(F, W)) :
    pushVal ρ ψ (h'.trans h) (resM F h' s) = resM N (ρ.preimage_mono h') (pushVal ρ ψ h s) :=
  homApp_resM ψ h h' s

def backPush {V : X.Opens} (ψ : Γ(homMod F ((Scheme.Modules.pushforward ρ).obj N), V)) :
    F ⟶ (Scheme.Modules.pushforward ρ).obj (cutN N (ρ ⁻¹ᵁ V)) :=
  homOfLinear (fun W =>
    { toFun s := (cutNEquiv N (ρ ⁻¹ᵁ V) (ρ ⁻¹ᵁ W)).symm
        (resM N (cutO_le_inf ρ V W) (pushVal ρ ψ inf_le_right (resM F inf_le_left s)))
      map_add' s t := by rw [map_add, pushVal_add, map_add, map_add] <;> rfl
      map_smul' a s := (cutNEquiv N (ρ ⁻¹ᵁ V) (ρ ⁻¹ᵁ W)).injective (by
        refine Eq.trans ?_ (cutNEquiv_smul _ _ _ (ρ.app W a) _).symm
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, resM_smul, pushVal_smul,
          resM_smul, app_resG, resG_resG] <;> rfl) })
    fun {W W'} h s => (cutNEquiv N (ρ ⁻¹ᵁ V) (ρ ⁻¹ᵁ W')).injective (by
      change resM N (cutO_le_inf ρ V W')
          (pushVal ρ ψ inf_le_right (resM F inf_le_left (resM F h s))) =
        resM N (cutO_mono _ (ρ.preimage_mono h))
          (resM N (cutO_le_inf ρ V W) (pushVal ρ ψ inf_le_right (resM F inf_le_left s)))
      rw [resM_resM (F := F), resM_resM (F := N),
        ← resM_resM (F := F) inf_le_left (inf_le_inf_right V h), pushVal_res, resM_resM (F := N)])

theorem fwdSec_surjective (V : X.Opens) :
    Function.Surjective (fwdSec ρ (F := F) (N := N) (V := V)) := fun ψ =>
  ⟨ofCutN (adj ρ (backPush ρ ψ)), hom_ext fun W h s => by
    rw [homApp_fwdSec, homApp_ofCutN, adj_app]
    change resM N _ (resM N (cutO_mono _ le_rfl) (resM N (cutO_le_inf ρ V W)
      (pushVal ρ ψ inf_le_right (resM F inf_le_left s)))) = pushVal ρ ψ h s
    rw [resM_resM (F := N), resM_resM (F := N)]
    have := pushVal_res ρ ψ inf_le_right (le_inf le_rfl h : W ≤ W ⊓ V) (resM F inf_le_left s)
    rw [resM_resM (F := F), resM_self] at this
    exact this.symm⟩

variable (F N) in
instance isIso_fwdHom : IsIso (fwdHom ρ F N) :=
  Twist.isIso_of_bijective _ fun V => ⟨fwdSec_injective ρ F N V, fwdSec_surjective ρ V⟩

end GlobalTheory.HomPull

namespace GlobalTheory.HomPull

variable {X Y : Scheme.{0}} (ρ : Y ⟶ X) (F : X.Modules) (N : Y.Modules)

def pushHomIso : (Scheme.Modules.pushforward ρ).obj (homMod ((Scheme.Modules.pullback ρ).obj F) N) ≅
    homMod F ((Scheme.Modules.pushforward ρ).obj N) :=
  asIso (fwdHom ρ F N)

theorem nonempty_pushforward_homMod_iso : ∀ (X Y : Scheme.{0}) (ρ : Y ⟶ X) (W : X.Modules) (N : Y.Modules), Nonempty ((Scheme.Modules.pushforward ρ).obj (homMod ((Scheme.Modules.pullback ρ).obj W) N) ≅ homMod W ((Scheme.Modules.pushforward ρ).obj N)) :=
  fun _ _ ρ W N => ⟨pushHomIso ρ W N⟩

end GlobalTheory.HomPull
