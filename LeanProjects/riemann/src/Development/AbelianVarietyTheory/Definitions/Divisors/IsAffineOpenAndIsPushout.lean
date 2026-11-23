import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameOfProjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self homOfLinear homOfLinear_app)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.QCoh (IsFiniteQC pullbackSections appLEAlgebra)
open GlobalTheory.DualPull (adj adj_app pull_ext appLE_resG resG_appLE)
open GlobalTheory.VB

namespace GlobalTheory.Conormal

variable {S S' S'' X X' X'' : Scheme.{0}}

theorem appLE_appLE {f : X'' ⟶ X'} {g : X' ⟶ X} {k : X'' ⟶ X} (w : f ≫ g = k) {U : X.Opens}
    {V : X'.Opens} {W : X''.Opens} (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ k ⁻¹ᵁ U)
    (a : Γ(X, U)) : f.appLE V W e₂ (g.appLE U V e₁ a) = k.appLE U W e₃ a := by
  subst w
  exact congr($(Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂) a)

theorem id_appLE {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (𝟙 X : X ⟶ X).appLE U V h a = resG X h a := rfl

theorem le_preimage_of_comp {f : X'' ⟶ X'} {g : X' ⟶ X} {k : X'' ⟶ X} (w : f ≫ g = k)
    {U : X.Opens} {W : X''.Opens} : W ≤ f ⁻¹ᵁ g ⁻¹ᵁ U ↔ W ≤ k ⁻¹ᵁ U := by
  subst w; rfl

section Def

variable (e : S ⟶ X) {U V V' : S.Opens} {T W W' : X.Opens}

def idealSub : Sub (structureModule X) where
  sec W := (RingHom.ker (e.appLE W (e ⁻¹ᵁ W) le_rfl).hom : Ideal Γ(X, W))
  res_mem {V W} h s hs := by
    revert s
    intro (s : Γ(X, V)) hs
    change e.appLE W _ le_rfl (resG X h s) = 0
    rw [appLE_resG, ← resG_appLE e (e.preimage_mono h) le_rfl,
      show e.appLE V _ le_rfl s = 0 from hs, map_zero]
  mem_of_local {V s} H := by
    choose W hW hx hs using fun x : (e ⁻¹ᵁ V) => H (e x) x.2
    refine LB.fun_ext_of_cover (fun x => e ⁻¹ᵁ W x) (fun x => e.preimage_mono (hW x))
      (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx _⟩) fun x => ?_
    rw [map_zero]
    exact (resG_appLE e _ _ _).trans ((appLE_resG e (hW x) le_rfl s).symm.trans (hs x))

abbrev ideal : X.Modules := (idealSub e).toMod

instance isQuasicoherent_ideal [QuasiCompact e] : (ideal e).IsQuasicoherent := by
  have := (isVB_structureModule X).isQuasicoherent
  refine Sub.isQuasicoherent _ fun U hU f (t : Γ(X, U)) ht => ?_
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact S
    (U := e ⁻¹ᵁ U) (e.isCompact_preimage hU.isCompact) (e.appLE U _ le_rfl t)
    (e.appLE U _ le_rfl f) (by
      have hle : S.basicOpen (e.appLE U _ le_rfl f) ≤ e ⁻¹ᵁ X.basicOpen f := by
        rw [Scheme.Hom.appLE_eq_app, e.preimage_basicOpen]
      have := congrArg (resG S hle)
        (show e.appLE _ _ le_rfl (resG X (X.basicOpen_le f) t) = 0 from ht)
      rw [resG_appLE, appLE_resG, map_zero] at this
      exact (resG_appLE e _ _ _).trans this)
  refine ⟨n, ?_⟩
  change e.appLE U _ le_rfl (f ^ n * t) = 0
  rw [map_mul, map_pow, hn]

def conormal : S.Modules := (Scheme.Modules.pullback e).obj (ideal e)

instance isQuasicoherent_conormal [QuasiCompact e] : (conormal e).IsQuasicoherent :=
  QCoh.isQuasicoherent_pullback e (ideal e)

variable {e}

def cls (h : V ≤ e ⁻¹ᵁ W) (f : Γ(X, W)) (hf : e.appLE W _ le_rfl f = 0) : Γ(conormal e, V) :=
  pullbackSections e (ideal e) h ((idealSub e).mkSec (V := W) f hf)

theorem resM_cls (h : V ≤ e ⁻¹ᵁ W) (h' : V' ≤ V) (f : Γ(X, W)) (hf) :
    resM _ h' (cls h f hf) = cls (h'.trans h) f hf :=
  QCoh.res_pullbackSections e (ideal e) h h' _

theorem cls_congr (h : V ≤ e ⁻¹ᵁ W) (h' : V ≤ e ⁻¹ᵁ W') (hT : V ≤ e ⁻¹ᵁ T) (k : T ≤ W)
    (k' : T ≤ W') {f : Γ(X, W)} {f' : Γ(X, W')} (hf hf') (H : resG X k f = resG X k' f') :
    cls h f hf = cls h' f' hf' :=
  (QCoh.pullbackSections_res e (ideal e) hT k _).symm.trans <|
    (congrArg (pullbackSections e (ideal e) hT) ((idealSub e).incl_app_injective T
      ((app_resM _ _ _).trans (H.trans (app_resM (idealSub e).incl k'
        ((idealSub e).mkSec (V := W') f' hf')).symm)))).trans
      (QCoh.pullbackSections_res e (ideal e) hT k' _)

theorem cls_add (h : V ≤ e ⁻¹ᵁ W) (f g : Γ(X, W)) (hf hg hfg) :
    cls h (f + g) hfg = cls h f hf + cls h g hg :=
  letI := QCoh.appLEModule e ((Scheme.Modules.pullback e).obj (ideal e)) h
  (pullbackSections e (ideal e) h).map_add ((idealSub e).mkSec (V := W) f hf)
    ((idealSub e).mkSec (V := W) g hg)

theorem cls_mul (h : V ≤ e ⁻¹ᵁ W) (a f : Γ(X, W)) (hf haf) :
    cls h (a * f) haf = e.appLE W V h a • cls h f hf :=
  QCoh.pullbackSections_smul e (ideal e) h a ((idealSub e).mkSec (V := W) f hf)

theorem cls_zero (h : V ≤ e ⁻¹ᵁ W) {f : Γ(X, W)} (hf) (h0 : f = 0) : cls h f hf = 0 := by
  subst h0
  simpa using cls_mul h 0 0 hf (by simpa using hf)

variable {π : X ⟶ S} (he : e ≫ π = 𝟙 S)
include he

theorem le_preimage_iff : V ≤ e ⁻¹ᵁ π ⁻¹ᵁ U ↔ V ≤ U := le_preimage_of_comp he

theorem appLE_base (h : V ≤ e ⁻¹ᵁ W) (k : W ≤ π ⁻¹ᵁ U) (hV : V ≤ U) (a : Γ(S, U)) :
    e.appLE W V h (π.appLE U W k a) = resG S hV a := appLE_appLE he k h hV a

theorem le_nhd (h : V ≤ e ⁻¹ᵁ W) : V ≤ e ⁻¹ᵁ (W ⊓ π ⁻¹ᵁ e ⁻¹ᵁ W) :=
  le_inf h ((le_preimage_iff he).2 h)

omit he in
variable (e π W) in

def center : Γ(X, W) →+ Γ(X, W ⊓ π ⁻¹ᵁ e ⁻¹ᵁ W) :=
  (resG X inf_le_left).toAddMonoidHom -
    ((π.appLE _ _ inf_le_right).hom.comp (e.appLE W _ le_rfl).hom).toAddMonoidHom

omit he in

theorem center_apply (f : Γ(X, W)) : center e W π f =
    resG X inf_le_left f - π.appLE _ _ inf_le_right (e.appLE W _ le_rfl f) := rfl

theorem appLE_center (f : Γ(X, W)) : e.appLE _ _ le_rfl (center e W π f) = 0 := by
  rw [center_apply, map_sub, appLE_resG, appLE_base he _ _ (e.preimage_mono inf_le_left),
    resG_appLE, sub_self]

def d (h : V ≤ e ⁻¹ᵁ W) : Γ(X, W) →+ Γ(conormal e, V) :=
  AddMonoidHom.mk' (fun f => cls (le_nhd he h) (center e W π f) (appLE_center he f)) fun f g => by
    simp only [map_add]
    exact cls_add _ _ _ _ _ _

theorem d_apply (h : V ≤ e ⁻¹ᵁ W) (f : Γ(X, W)) :
    d he h f = cls (le_nhd he h) (center e W π f) (appLE_center he f) := rfl

theorem d_eq_cls (h : V ≤ e ⁻¹ᵁ W) (f : Γ(X, W)) (hf : e.appLE W _ le_rfl f = 0) :
    d he h f = cls h f hf :=
  cls_congr _ _ (le_nhd he h) le_rfl inf_le_left _ _ (by
    rw [resG_self, center_apply, hf, map_zero, sub_zero])

end Def

variable {π : X ⟶ S} {e : S ⟶ X} {F F' : S.Modules} {U V V' : S.Opens} {W W' : X.Opens}

variable (π e F) in

@[ext] structure Der where

  app {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) : Γ(X, W) →+ Γ(F, V)

  res_app {W : X.Opens} {V V' : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (h' : V' ≤ V) (f : Γ(X, W)) :
    resM F h' (app h f) = app (h'.trans h) f

  app_res {W W' : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W') (k : W' ≤ W) (f : Γ(X, W)) :
    app h (resG X k f) = app (h.trans (e.preimage_mono k)) f

  app_mul {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (f g : Γ(X, W)) :
    app h (f * g) = e.appLE W V h f • app h g + e.appLE W V h g • app h f

  app_base {W : X.Opens} {V U : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (k : W ≤ π ⁻¹ᵁ U) (a : Γ(S, U)) :
    app h (π.appLE U W k a) = 0

variable (he : e ≫ π = 𝟙 S)

def univ : Der π e (conormal e) where
  app h := d he h
  res_app h h' f := resM_cls _ h' _ _
  app_res {W W' V} h k f := cls_congr _ _ (le_nhd he h) le_rfl
    (inf_le_inf k (π.preimage_mono (e.preimage_mono k))) _ _ (by
      rw [resG_self, center_apply, center_apply, map_sub, resG_resG, resG_resG, resG_appLE,
        appLE_resG, ← resG_appLE e (e.preimage_mono k) le_rfl, appLE_resG])
  app_mul {W V} h f g := by
    have h₁ := cls_mul (le_nhd he h) (resG X inf_le_left f) _ (appLE_center he g)
      (by rw [map_mul, appLE_center he, mul_zero])
    have h₂ := cls_mul (le_nhd he h) (π.appLE _ _ inf_le_right (e.appLE W _ le_rfl g)) _
      (appLE_center he f) (by rw [map_mul, appLE_center he, mul_zero])
    replace h₁ := h₁.trans (congrArg (· • _) (appLE_resG e _ _ f))
    replace h₂ := h₂.trans (congrArg (· • _) ((appLE_base he _ _ h _).trans (resG_appLE e _ _ g)))
    rw [d_apply, d_apply, d_apply, ← h₁, ← h₂, ← cls_add _ _ _ _ _ (by
      rw [map_add, map_mul, map_mul, appLE_center he, appLE_center he]; simp)]
    congr 1
    simp only [center_apply, map_mul]
    ring
  app_base {W V U} h k a := cls_zero _ _ (by
    rw [center_apply, appLE_base he _ _ ((le_preimage_iff he).1 (e.preimage_mono k)), resG_appLE,
      appLE_resG, sub_self])

theorem resM_d (h : V ≤ e ⁻¹ᵁ W) (h' : V' ≤ V) (f : Γ(X, W)) :
    resM _ h' (d he h f) = d he (h'.trans h) f := (univ he).res_app h h' f

theorem d_resG (h : V ≤ e ⁻¹ᵁ W') (k : W' ≤ W) (f : Γ(X, W)) :
    d he h (resG X k f) = d he (h.trans (e.preimage_mono k)) f := (univ he).app_res h k f

theorem d_mul (h : V ≤ e ⁻¹ᵁ W) (f g : Γ(X, W)) :
    d he h (f * g) = e.appLE W V h f • d he h g + e.appLE W V h g • d he h f :=
  (univ he).app_mul h f g

theorem d_base (h : V ≤ e ⁻¹ᵁ W) (k : W ≤ π ⁻¹ᵁ U) (a : Γ(S, U)) :
    d he h (π.appLE U W k a) = 0 := (univ he).app_base h k a

theorem d_one (h : V ≤ e ⁻¹ᵁ W) : d he h 1 = 0 := by
  simpa using d_base he (U := ⊤) h le_top 1

theorem hom_ext {φ ψ : conormal e ⟶ F} (H : ∀ (W : X.Opens) (f : Γ(X, W)),
    φ.app _ (d he (le_refl (e ⁻¹ᵁ W)) f) = ψ.app _ (d he le_rfl f)) : φ = ψ :=
  pull_ext e fun W s => by
    have := H W ((idealSub e).incl.app W s)
    rwa [d_eq_cls he _ _ ((idealSub e).incl_app_mem s)] at this

namespace Der

def lift (D : Der π e F) : conormal e ⟶ F :=
  adj e (homOfLinear (F := ideal e) (G := (Scheme.Modules.pushforward e).obj F)
    (fun W =>
      { toFun s := D.app (le_refl (e ⁻¹ᵁ W)) ((idealSub e).incl.app W s)
        map_add' s t := by rw [map_add]; exact map_add _ _ _
        map_smul' a s := by
          refine (D.app_mul _ a ((idealSub e).incl.app W s)).trans ?_
          rw [show e.appLE W _ le_rfl ((idealSub e).incl.app W s) = 0 from
            (idealSub e).incl_app_mem s, zero_smul, add_zero, Scheme.Hom.appLE_eq_app]
          rfl })
    fun {W W'} h s => (D.app_res le_rfl h _).trans (D.res_app le_rfl (e.preimage_mono h) _).symm)

theorem lift_d (D : Der π e F) (h : V ≤ e ⁻¹ᵁ W) (f : Γ(X, W)) :
    D.lift.app V (d he h f) = D.app h f := by
  refine (adj_app e _ _ _).trans ((D.res_app le_rfl _ (center e W π f)).trans ?_)
  rw [center_apply, map_sub, D.app_res, D.app_base, sub_zero]

def comp (D : Der π e F) (φ : F ⟶ F') : Der π e F' where
  app {W V} h := (QCoh.appLinear φ V).toAddMonoidHom.comp (D.app h)
  res_app h h' f := (app_resM φ h' _).symm.trans (congrArg (φ.app _) (D.res_app h h' f))
  app_res h k f := congrArg (φ.app _) (D.app_res h k f)
  app_mul {W V} h f g := (congrArg (QCoh.appLinear φ V) (D.app_mul h f g)).trans (by
    rw [map_add, map_smul, map_smul]; rfl)
  app_base h k a := (congrArg (φ.app _) (D.app_base h k a)).trans (map_zero _)

end Der

variable (F) in

def homEquivDer : (conormal e ⟶ F) ≃ Der π e F where
  toFun := (univ he).comp
  invFun := Der.lift
  left_inv φ := hom_ext he fun _ _ => Der.lift_d he _ _ _
  right_inv D := by
    ext W V h f
    exact D.lift_d he h f

theorem homEquivDer_app (φ : conormal e ⟶ F) (h : V ≤ e ⁻¹ᵁ W) (f : Γ(X, W)) :
    (homEquivDer F he φ).app h f = φ.app V (d he h f) := rfl

section Map

variable {π' : X' ⟶ S} {e' : S ⟶ X'} {π'' : X'' ⟶ S} {e'' : S ⟶ X''} {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

def Der.pull (D : Der π' e' F) (w : φ ≫ π = π') (we : e' ≫ φ = e) : Der π e F where
  app {W V} h := (D.app ((le_preimage_of_comp we).2 h)).comp
    (φ.appLE W _ le_rfl).hom.toAddMonoidHom
  res_app h h' f := D.res_app _ h' _
  app_res {W W' V} h k f := (congrArg (D.app _) ((appLE_resG φ k _ f).trans
    (resG_appLE φ (φ.preimage_mono k) le_rfl f).symm)).trans (D.app_res _ _ _)
  app_mul {W V} h f g := (congrArg (D.app _) (map_mul (φ.appLE W _ le_rfl).hom f g)).trans
    ((D.app_mul _ _ _).trans (by rw [appLE_appLE we _ _ h, appLE_appLE we _ _ h]; rfl))
  app_base h k a := (congrArg (D.app _) (appLE_appLE w k _
    ((le_preimage_of_comp w).1 (φ.preimage_mono k)) a)).trans (D.app_base _ _ _)

variable (he' : e' ≫ π' = 𝟙 S) (w : φ ≫ π = π') (we : e' ≫ φ = e)

def map : conormal e ⟶ conormal e' := ((univ he').pull w we).lift

theorem map_d (h : V ≤ e ⁻¹ᵁ W) {W' : X'.Opens} (h' : V ≤ e' ⁻¹ᵁ W') (k : W' ≤ φ ⁻¹ᵁ W)
    (f : Γ(X, W)) : (map he' w we).app V (d he h f) = d he' h' (φ.appLE W W' k f) :=
  (Der.lift_d he _ h f).trans
    ((congrArg _ (resG_appLE φ k le_rfl f)).symm.trans (d_resG he' h' k _)).symm

theorem map_id {φ : X ⟶ X} (hφ : φ = 𝟙 X) (w : φ ≫ π = π) (we : e ≫ φ = e) :
    map he w we = 𝟙 _ := by
  subst hφ
  exact hom_ext he fun W f => (map_d he he w we _ le_rfl le_rfl f).trans
    (congrArg _ (resG_self _ f))

include he in

theorem map_comp (he'' : e'' ≫ π'' = 𝟙 S) (w' : ψ ≫ π' = π'') (we' : e'' ≫ ψ = e')
    {χ : X'' ⟶ X} (hχ : ψ ≫ φ = χ) (w'' : χ ≫ π = π'') (we'' : e'' ≫ χ = e) :
    map he' w we ≫ map he'' w' we' = map he'' w'' we'' :=
  hom_ext he fun W f => by
    have h' := (le_preimage_of_comp we).2 (le_refl (e ⁻¹ᵁ W))
    have h'' := (le_preimage_of_comp we').2 h'
    rw [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply, map_d he he' w we _ h' le_rfl,
      map_d he' he'' w' we' _ h'' le_rfl, map_d he he'' w'' we'' _ h''
        ((le_preimage_of_comp hχ).1 le_rfl), appLE_appLE hχ]

include he in

theorem map_eq_zero (hφ : π' ≫ e = φ) : map he' w we = 0 :=
  hom_ext he fun W f => by
    have k := (le_preimage_of_comp hφ).2 (le_refl (φ ⁻¹ᵁ W))
    rw [map_d he he' w we _ ((le_preimage_of_comp we).2 le_rfl) le_rfl,
      ← appLE_appLE hφ le_rfl k, d_base]
    rfl

end Map

section Base

variable {π' : X' ⟶ S'} {e' : S' ⟶ X'} {φ : X' ⟶ X} {f : S' ⟶ S}

theorem le_of_sq (we : e' ≫ φ = f ≫ e) (h : V ≤ e ⁻¹ᵁ W) {T : S'.Opens} (hT : T ≤ f ⁻¹ᵁ V) :
    T ≤ e' ⁻¹ᵁ φ ⁻¹ᵁ W := (le_preimage_of_comp we).2 (hT.trans (f.preimage_mono h))

def Der.push {F : S'.Modules} (D : Der π' e' F) (w : φ ≫ π = π' ≫ f) (we : e' ≫ φ = f ≫ e) :
    Der π e ((Scheme.Modules.pushforward f).obj F) where
  app {W V} h := (D.app (le_of_sq we h le_rfl)).comp (φ.appLE W _ le_rfl).hom.toAddMonoidHom
  res_app h h' a := D.res_app _ (f.preimage_mono h') _
  app_res {W W' V} h k a := (congrArg (D.app _) ((appLE_resG φ k _ a).trans
    (resG_appLE φ (φ.preimage_mono k) le_rfl a).symm)).trans (D.app_res _ _ _)
  app_mul {W V} h a b := by
    have (c : Γ(X, W)) : e'.appLE _ _ (le_of_sq we h le_rfl) (φ.appLE W _ le_rfl c) =
        f.app V (e.appLE W V h c) := by
      have k : f ⁻¹ᵁ V ≤ (f ≫ e) ⁻¹ᵁ W := f.preimage_mono h
      rw [appLE_appLE we _ _ k, ← Scheme.Hom.appLE_eq_app, appLE_appLE rfl _ _ k]
    have H := D.app_mul (le_of_sq we h le_rfl) (φ.appLE W _ le_rfl a) (φ.appLE W _ le_rfl b)
    rw [this, this, ← map_mul] at H
    exact H
  app_base {W V U} h k a := by
    have k' : φ ⁻¹ᵁ W ≤ (π' ≫ f) ⁻¹ᵁ U := (le_preimage_of_comp w).1 (φ.preimage_mono k)
    have H := D.app_base (le_of_sq we h le_rfl) ((le_preimage_of_comp rfl).2 k')
      (f.appLE U _ le_rfl a)
    rw [appLE_appLE rfl _ _ k', ← appLE_appLE w k le_rfl k'] at H
    exact H

variable (he' : e' ≫ π' = 𝟙 S') (w : φ ≫ π = π' ≫ f) (we : e' ≫ φ = f ≫ e)

def baseMap : (Scheme.Modules.pullback f).obj (conormal e) ⟶ conormal e' :=
  adj f ((univ he').push w we).lift

theorem baseMap_d (h : V ≤ e ⁻¹ᵁ W) {T : S'.Opens} (hT : T ≤ f ⁻¹ᵁ V) {W' : X'.Opens}
    (h' : T ≤ e' ⁻¹ᵁ W') (k : W' ≤ φ ⁻¹ᵁ W) (a : Γ(X, W)) :
    (baseMap he' w we).app T (pullbackSections f _ hT (d he h a)) =
      d he' h' (φ.appLE W W' k a) :=
  (adj_app f _ _ _).trans <| (congrArg (resM _ hT) (Der.lift_d he _ h a)).trans <|
    (resM_d he' (le_of_sq we h le_rfl) hT _).trans
      ((congrArg _ (resG_appLE φ k le_rfl a)).symm.trans (d_resG he' h' k _)).symm

theorem pullback_hom_ext {F : S'.Modules}
    {α β : (Scheme.Modules.pullback f).obj (conormal e) ⟶ F}
    (H : ∀ (W : X.Opens) (a : Γ(X, W)),
      α.app _ (pullbackSections f _ (le_refl (f ⁻¹ᵁ e ⁻¹ᵁ W)) (d he le_rfl a)) =
        β.app _ (pullbackSections f _ le_rfl (d he le_rfl a))) : α = β := by
  obtain ⟨α, rfl⟩ := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm.surjective α
  obtain ⟨β, rfl⟩ := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm.surjective β
  refine congrArg _ (hom_ext he fun W a => ?_)
  have := (adj_app f α _ _).symm.trans ((H W a).trans (adj_app f β _ _))
  exact (resM_self (F := F) le_rfl _).symm.trans (this.trans (resM_self le_rfl _))

end Base

variable (π e) in

structure IsChart (U : S.Opens) (W : X.Opens) : Prop where

  affine_base : IsAffineOpen U

  affine : IsAffineOpen W

  le : U ≤ e ⁻¹ᵁ W

  le_base : W ≤ π ⁻¹ᵁ U

theorem isAffineOpen_and_isPushout {Y T : Scheme.{0}} {f : T ⟶ S} {g : Y ⟶ X} {p : Y ⟶ T}
    (H : IsPullback g p π f) {T₀ : T.Opens} (hU : IsAffineOpen U) (hT : IsAffineOpen T₀)
    (hW : IsAffineOpen W) (k : T₀ ≤ f ⁻¹ᵁ U) (k' : W ≤ π ⁻¹ᵁ U) :
    IsAffineOpen (g ⁻¹ᵁ W ⊓ p ⁻¹ᵁ T₀) ∧ IsPushout (π.appLE U W k') (f.appLE U T₀ k)
      (g.appLE W (g ⁻¹ᵁ W ⊓ p ⁻¹ᵁ T₀) inf_le_left) (p.appLE T₀ _ inf_le_right) := by
  refine ⟨?_, (isIso_pushoutSection_iff H k k' rfl).1
    (isIso_pushoutSection_of_isAffineOpen H k k' rfl hU hT hW)⟩
  have : IsAffine U := hU
  have : IsAffine T₀ := hT
  have : IsAffine W := hW
  exact .of_isIso (Scheme.Hom.isPullback_resLE H k k' rfl).isoPullback.hom

include he in

theorem exists_isChart_inf (hU : IsAffineOpen U) (hW : IsAffineOpen W) (k : W ≤ π ⁻¹ᵁ U) {x : S}
    (hx : e x ∈ W) (hV : x ∈ V) : ∃ U', x ∈ U' ∧ U' ≤ V ∧ U' ≤ U ∧ IsChart π e U' (W ⊓ π ⁻¹ᵁ U') := by
  obtain ⟨U', hU', hx', hle⟩ := QCoh.exists_affine_mem_le (U := V ⊓ e ⁻¹ᵁ W) x ⟨hV, hx⟩
  have h := (hle.trans inf_le_right).trans ((le_preimage_iff he).1 (e.preimage_mono k))
  exact ⟨U', hx', hle.trans inf_le_left, h, hU',
    (isAffineOpen_and_isPushout (IsPullback.id_horiz π) hU hU' hW h k).1,
    le_inf (hle.trans inf_le_right) ((le_preimage_iff he).2 le_rfl), inf_le_right⟩

include he in

theorem exists_isChart {x : S} (hV : x ∈ V) : ∃ U W, x ∈ U ∧ U ≤ V ∧ IsChart π e U W := by
  obtain ⟨U, hU, hx, -⟩ := QCoh.exists_affine_mem_le x hV
  obtain ⟨W, hW, hx', k⟩ := QCoh.exists_affine_mem_le (U := π ⁻¹ᵁ U) (e x)
    ((le_preimage_iff he).2 le_rfl hx)
  obtain ⟨U', h₁, h₂, -, c⟩ := exists_isChart_inf he hU hW k hx' hV
  exact ⟨U', _, h₁, h₂, c⟩

namespace IsChart

variable (c : IsChart π e U W)

abbrev algebra : Algebra Γ(S, U) Γ(X, W) := appLEAlgebra π c.le_base

def aug : letI := c.algebra; Γ(X, W) →ₐ[Γ(S, U)] Γ(S, U) :=
  letI := c.algebra
  { __ := (e.appLE W U c.le).hom
    commutes' a := (appLE_base he c.le c.le_base le_rfl a).trans (resG_self _ a) }

theorem aug_apply (a : Γ(X, W)) : c.aug he a = e.appLE W U c.le a := rfl

theorem aug_eq_zero_iff {a : Γ(X, W)} : c.aug he a = 0 ↔ e.appLE W _ le_rfl a = 0 :=
  ⟨fun h => (resG_appLE e ((le_preimage_iff he).1 (e.preimage_mono c.le_base)) c.le a).symm.trans
      ((congrArg _ h).trans (map_zero _)),
    fun h => (resG_appLE e c.le le_rfl a).symm.trans ((congrArg _ h).trans (map_zero _))⟩

def ofAugCot : letI := c.algebra; AugCot (c.aug he) →ₗ[Γ(S, U)] Γ(conormal e, U) :=
  letI := c.algebra
  AugCot.lift (c.aug he)
    { __ := d he c.le
      map_smul' r a := (d_mul he c.le (π.appLE U W c.le_base r) a).trans (by
        rw [d_base, smul_zero, add_zero, appLE_base he _ _ le_rfl, resG_self]; rfl) }
    (d_mul he c.le)

theorem ofAugCot_d (a : Γ(X, W)) :
    letI := c.algebra; c.ofAugCot he (AugCot.d (c.aug he) a) = d he c.le a :=
  letI := c.algebra
  AugCot.lift_d _ _ _ _

variable [QuasiCompact e]

theorem ofAugCot_bijective : Function.Bijective (c.ofAugCot he) := by
  letI := c.algebra
  letI := appLEAlgebra e c.le
  letI := QCoh.appLEModule e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := QCoh.appLE_isScalarTower e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := AugCot.isScalarTower_of_algebraMap_eq (c.aug he) fun _ => rfl
  have hb := QCoh.isBaseChange_pullbackSections e (ideal e) c.affine_base c.affine c.le
  let g : Γ(ideal e, W) →ₗ[Γ(X, W)] AugCot (c.aug he) := (RingHom.ker (c.aug he)).toCotangent ∘ₗ
    (QCoh.appLinear (idealSub e).incl W).codRestrict (RingHom.ker (c.aug he)) fun s =>
      (c.aug_eq_zero_iff he).2 ((idealSub e).incl_app_mem s)
  have key (x : RingHom.ker (c.aug he)) : c.ofAugCot he ((RingHom.ker (c.aug he)).toCotangent x) =
      cls c.le x ((c.aug_eq_zero_iff he).1 x.2) := d_eq_cls he _ _ _
  refine Function.bijective_iff_has_inverse.2 ⟨hb.lift g, fun x => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := (RingHom.ker (c.aug he)).toCotangent_surjective x
    rw [key]
    exact hb.lift_eq g _
  · refine hb.inductionOn y (fun y => c.ofAugCot he (hb.lift g y) = y) (by rw [map_zero, map_zero]; rfl) (fun s => ?_)
      (fun r y hy => ?_) fun y z hy hz => ?_
    · rw [hb.lift_eq]
      exact key _
    · rw [map_smul, map_smul, hy]
      rfl
    · rw [map_add, map_add, hy, hz]
      rfl

def augCotEquiv : letI := c.algebra; AugCot (c.aug he) ≃ₗ[Γ(S, U)] Γ(conormal e, U) :=
  letI := c.algebra
  LinearEquiv.ofBijective _ (c.ofAugCot_bijective he)

theorem augCotEquiv_d (a : Γ(X, W)) :
    letI := c.algebra; c.augCotEquiv he (AugCot.d (c.aug he) a) = d he c.le a := c.ofAugCot_d he a

theorem d_surjective : Function.Surjective (d he c.le) := fun s => by
  letI := c.algebra
  obtain ⟨x, rfl⟩ := (c.augCotEquiv he).surjective s
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ x
  exact ⟨a, (c.augCotEquiv_d he a).symm⟩

open scoped TensorProduct in

def kaehlerEquiv : letI := c.algebra; letI := appLEAlgebra e c.le
    Γ(conormal e, U) ≃ₗ[Γ(S, U)] Γ(S, U) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, U)] :=
  letI := c.algebra
  letI := appLEAlgebra e c.le
  (c.augCotEquiv he).symm ≪≫ₗ AugCot.kaehlerEquiv (c.aug he) fun _ => rfl

open scoped TensorProduct in

theorem kaehlerEquiv_d (a : Γ(X, W)) : letI := c.algebra; letI := appLEAlgebra e c.le
    c.kaehlerEquiv he (d he c.le a) = 1 ⊗ₜ KaehlerDifferential.D _ _ a := by
  letI := c.algebra
  letI := appLEAlgebra e c.le
  rw [← c.augCotEquiv_d he, kaehlerEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact AugCot.kaehlerEquiv_d _ _ a

end IsChart

theorem hom_ext_of_local {α β : F ⟶ F'} (H : ∀ (V : S.Opens) (x : S), x ∈ V →
    ∃ U : S.Opens, x ∈ U ∧ U ≤ V ∧ ∀ s, α.app U s = β.app U s) : α = β := by
  ext V s
  choose U hx hle hs using fun x : V => H V x x.2
  refine sec_ext_of_cover U hle (fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩) fun x => ?_
  exact (app_resM α _ s).symm.trans ((hs x _).trans (app_resM β _ s))

theorem prod_hom_ext {Y P : Scheme.{0}} {π₂ : Y ⟶ S} {e₂ : S ⟶ Y} (he₂ : e₂ ≫ π₂ = 𝟙 S)
    {p₁ : P ⟶ X} {p₂ : P ⟶ Y} (H : IsPullback p₁ p₂ π π₂) {q : P ⟶ S} {s : S ⟶ P} [QuasiCompact s]
    (hs : s ≫ q = 𝟙 S) (w₁ : p₁ ≫ π = q) (w₂ : p₂ ≫ π₂ = q) (v₁ : s ≫ p₁ = e) (v₂ : s ≫ p₂ = e₂)
    {α β : conormal s ⟶ F} (h₁ : map hs w₁ v₁ ≫ α = map hs w₁ v₁ ≫ β)
    (h₂ : map hs w₂ v₂ ≫ α = map hs w₂ v₂ ≫ β) : α = β := by
  have he : e ≫ π = 𝟙 S := by rw [← v₁, Category.assoc, w₁, hs]
  refine hom_ext_of_local fun V x hx => ?_
  obtain ⟨U₁, W₁, hx₁, hle₁, c₁⟩ := exists_isChart he hx
  obtain ⟨U, W₂, hx₂, hle₂, c₂⟩ := exists_isChart he₂ hx₁
  have k₂ := c₂.le_base.trans (π₂.preimage_mono hle₂)
  obtain ⟨hW, po⟩ := isAffineOpen_and_isPushout H c₁.affine_base c₂.affine c₁.affine k₂ c₁.le_base
  have c : IsChart q s U (p₁ ⁻¹ᵁ W₁ ⊓ p₂ ⁻¹ᵁ W₂) := ⟨c₂.affine_base, hW,
    le_inf ((le_preimage_of_comp v₁).2 (hle₂.trans c₁.le)) ((le_preimage_of_comp v₂).2 c₂.le),
    (le_preimage_of_comp w₂).1 (inf_le_right.trans (p₂.preimage_mono c₂.le_base))⟩
  refine ⟨U, hx₂, hle₂.trans hle₁, fun t => ?_⟩
  obtain ⟨a, rfl⟩ := c.d_surjective hs t
  have ha := (CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top a)
  induction ha using Subring.closure_induction with
  | mem a ha =>
    rcases ha with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [← map_d he hs w₁ v₁ (hle₂.trans c₁.le)]
      exact congr(($h₁).app U _)
    · rw [← map_d he₂ hs w₂ v₂ c₂.le]
      exact congr(($h₂).app U _)
  | zero => simp only [map_zero]
  | one => simp only [d_one, map_zero]
  | add a b _ _ ha hb => simp only [map_add, ha, hb]
  | neg a _ ha => simp only [map_neg, ha]
  | mul a b _ _ ha hb => simp only [d_mul, map_add, Scheme.Modules.Hom.app_smul, ha, hb]

theorem IsChart.exists_isBaseChange [QuasiCompact e] (c : IsChart π e U W) {R A : Type}
    [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) [Algebra R Γ(S, U)]
    [Module R Γ(conormal e, U)] [IsScalarTower R Γ(S, U) Γ(conormal e, U)] (α : A →+* Γ(X, W))
    (po : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R Γ(S, U)))
      (CommRingCat.ofHom α) (π.appLE U W c.le_base))
    (hα : ∀ a, e.appLE W U c.le (α a) = algebraMap R Γ(S, U) (ε a)) :
    ∃ l : AugCot ε →ₗ[R] Γ(conormal e, U), IsBaseChange Γ(S, U) l ∧
      ∀ a, l (AugCot.d ε a) = d he c.le (α a) := by
  letI := c.algebra
  letI := α.toAlgebra
  letI : Algebra R Γ(X, W) := (α.comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A Γ(X, W) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R Γ(S, U) Γ(X, W) := .of_algebraMap_eq fun r => congr($(po.w) r)
  haveI : Algebra.IsPushout R Γ(S, U) A Γ(X, W) := (CommRingCat.isPushout_iff_isPushout.1 po).symm
  have hb := AugCot.isBaseChange_of_isPushout (ε := ε) (ε' := c.aug he) hα
  refine ⟨(c.augCotEquiv he).toLinearMap.restrictScalars R ∘ₗ
    AugCot.mapBase (ε' := c.aug he) (IsScalarTower.toAlgHom R A Γ(X, W)) hα,
    .of_equiv (hb.equiv ≪≫ₗ c.augCotEquiv he) fun x => ?_, fun a => ?_⟩
  · simp
  · exact (congrArg (c.augCotEquiv he) (AugCot.mapBase_d _ _ a)).trans (c.augCotEquiv_d he _)

theorem IsChart.isFrame_d [QuasiCompact e] (c : IsChart π e U W) {R A ι : Type} [Fintype ι]
    [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) (ρ : R →+* Γ(S, U))
    (α : A →+* Γ(X, W))
    (po : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom α) (π.appLE U W c.le_base))
    (hα : ∀ a, e.appLE W U c.le (α a) = ρ (ε a)) (b : Module.Basis ι R (AugCot ε)) (a : ι → A)
    (hb : ∀ i, b i = AugCot.d ε (a i)) : IsFrame fun i => d he c.le (α (a i)) := by
  letI := ρ.toAlgebra
  letI : Module R Γ(conormal e, U) := Module.compHom _ ρ
  haveI : IsScalarTower R Γ(S, U) Γ(conormal e, U) := .of_algebraMap_smul fun _ _ => rfl
  obtain ⟨l, hl, hd⟩ := c.exists_isBaseChange he ε α po hα
  convert Summand.isFrame_of_affine_basis c.affine_base (hl.basis b) using 2 with i
  rw [IsBaseChange.basis_apply, hb, hd]

include he in

theorem isIso_baseMap {π' : X' ⟶ S'} {e' : S' ⟶ X'} {φ : X' ⟶ X} {f : S' ⟶ S} [QuasiCompact e]
    [QuasiCompact e'] (he' : e' ≫ π' = 𝟙 S') (H : IsPullback φ π' π f) (we : e' ≫ φ = f ≫ e) :
    IsIso (baseMap he' H.w we) := by
  have key (V : S'.Opens) (x : S') (hx : x ∈ V) : ∃ T : S'.Opens, x ∈ T ∧ T ≤ V ∧
      Function.Bijective ((baseMap he' H.w we).app T) := by
    obtain ⟨U, W, hxU, -, c⟩ := exists_isChart he (x := f x) (V := ⊤) trivial
    obtain ⟨T, hT, hxT, hle⟩ := QCoh.exists_affine_mem_le (U := V ⊓ f ⁻¹ᵁ U) x ⟨hx, hxU⟩
    have k := hle.trans inf_le_right
    obtain ⟨hW, po⟩ := isAffineOpen_and_isPushout H c.affine_base hT c.affine k c.le_base
    have c' : IsChart π' e' T (φ ⁻¹ᵁ W ⊓ π' ⁻¹ᵁ T) := ⟨hT, hW,
      le_inf (le_of_sq we c.le k) ((le_preimage_iff he').2 le_rfl), inf_le_right⟩
    refine ⟨T, hxT, hle.trans inf_le_left, ?_⟩
    letI := c.algebra
    letI := appLEAlgebra f k
    letI := QCoh.appLEModule f (conormal e') k
    haveI := QCoh.appLE_isScalarTower f (conormal e') k
    letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj (conormal e)) k
    haveI := QCoh.appLE_isScalarTower f ((Scheme.Modules.pullback f).obj (conormal e)) k
    obtain ⟨l, hl, hd⟩ := c'.exists_isBaseChange he' (c.aug he) (φ.appLE W _ inf_le_left).hom po
      fun a => by
        have k' : T ≤ (f ≫ e) ⁻¹ᵁ W := k.trans (f.preimage_mono c.le)
        exact (appLE_appLE we _ _ k' a).trans (appLE_appLE rfl c.le k k' a).symm
    have hb := QCoh.isBaseChange_pullbackSections f (conormal e) hT c.affine_base k
    have : QCoh.appLinear (baseMap he' H.w we) T = (hb.equiv.symm ≪≫ₗ
        (c.augCotEquiv he).symm.baseChange _ _ _ _ ≪≫ₗ hl.equiv).toLinearMap :=
      hb.algHom_ext _ _ fun s => by
        obtain ⟨a, rfl⟩ := c.d_surjective he s
        refine (baseMap_d he he' H.w we c.le k c'.le inf_le_left a).trans ?_
        simp [← c.augCotEquiv_d he, hd]
    change Function.Bijective (QCoh.appLinear (baseMap he' H.w we) T)
    rw [this]
    exact LinearEquiv.bijective _
  have := QCoh.mono_of_locally_app_injective _ fun V x hx =>
    (key V x hx).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  have := QCoh.epi_of_locally_app_surjective _ fun V x hx =>
    (key V x hx).imp fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩
  exact isIso_of_mono_of_epi _

include he in

theorem exists_isFrame [QuasiCompact e] [Smooth π] (x : S) :
    ∃ (U : S.Opens) (n : ℕ) (s : Fin n → Γ(conormal e, U)), x ∈ U ∧ IsFrame s := by
  obtain ⟨U, W, hx, -, c⟩ := exists_isChart he (x := x) (V := ⊤) trivial
  letI := c.algebra
  have : Algebra.Smooth Γ(S, U) Γ(X, W) := Smooth.smooth_appLE π c.affine_base c.affine c.le_base
  have := Module.Finite.equiv (c.augCotEquiv he)
  have := Module.Projective.of_equiv (c.augCotEquiv he)
  exact Summand.exists_frame_of_projective c.affine_base ⟨x, hx⟩

include he in

theorem isVB_conormal [QuasiCompact e] (n : ℕ) [h : SmoothOfRelativeDimension n π] :
    IsVB (conormal e) n := fun x => by
  obtain ⟨U, hU, W, hW, hx, k, hs⟩ := h.exists_isStandardSmoothOfRelativeDimension (e x)
  obtain ⟨U', hx', -, hle, c⟩ := exists_isChart_inf he hU hW k hx (V := ⊤) trivial
  have po := (isAffineOpen_and_isPushout (IsPullback.id_horiz π) hU c.affine_base hW hle k).2
  letI := c.algebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(S, U') Γ(X, W ⊓ π ⁻¹ᵁ U') :=
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n)).of_isPushout
      po.flip hs
  obtain ⟨b⟩ := AugCot.nonempty_basis_of_isStandardSmoothOfRelativeDimension (c.aug he) n
  exact ⟨U', _, hx', Summand.isFrame_of_affine_basis c.affine_base (b.map (c.augCotEquiv he))⟩

include he in

theorem exists_isVB_conormal [QuasiCompact e] [Smooth π] [PreconnectedSpace S] :
    ∃ n, IsVB (conormal e) n := by
  let r (x : S) := Module.finrank (S.presheaf.stalk x) ((conormal e).presheaf.stalk x :)
  have hr {U : S.Opens} {n : ℕ} {s : Fin n → Γ(conormal e, U)} (hs : IsFrame s) {x : S}
      (hx : x ∈ U) : r x = n := by simpa using Module.finrank_eq_card_basis (hs.stalkBasis x hx)
  have hc : IsLocallyConstant r := (IsLocallyConstant.iff_exists_open r).2 fun x =>
    have ⟨U, _, _, hx, hs⟩ := exists_isFrame he x
    ⟨U, U.isOpen, hx, fun _ hy => (hr hs hy).trans (hr hs hx).symm⟩
  obtain ⟨n, hn⟩ := hc.exists_eq_const
  refine ⟨n, fun x => ?_⟩
  obtain ⟨U, m, s, hx, hs⟩ := exists_isFrame he x
  obtain rfl : m = n := (hr hs hx).symm.trans (congrFun hn x)
  exact ⟨U, s, hx, hs⟩

theorem isZero_conormal_id : IsZero (conormal (𝟙 S)) :=
  (IsZero.iff_id_eq_zero _).2 ((map_id (Category.comp_id (𝟙 S)) rfl (Category.comp_id _)
    (Category.comp_id _)).symm.trans (map_eq_zero (Category.comp_id _) _ _ _ (Category.comp_id _)))

end GlobalTheory.Conormal
