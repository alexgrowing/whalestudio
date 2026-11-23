import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod homOfSec secOfHom homCoord)
open GlobalTheory.VB (IsVB IsFrame Chart det)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.LinePow

variable {X : Scheme.{0}}

theorem res_pow_mul_inv {L M : LB X} (n : ℕ) (p p' : M.ι) (q q' : L.ι)
    (h : M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q') ≤ M.U p ⊓ M.U p')
    (h' : M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q') ≤ L.U q ⊓ L.U q') :
    (res h (M.g p p' ^ (n : ℤ)) * (res h' (L.g q q' ^ (n : ℤ)))⁻¹ :
      Γ(X, M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q'))ˣ) = (res h (M.g p p') * (res h' (L.g q q'))⁻¹) ^ n := by
  rw [map_zpow, map_zpow, zpow_natCast, zpow_natCast, mul_pow, inv_pow]

def secPow {L M : LB X} (w : LB.Sec (LB.div M L)) (n : ℕ) :
    LB.Sec (LB.div (GlobalTheory.AbLaw.pw M n) (GlobalTheory.AbLaw.pw L n)) where
  f q := w.f q ^ n
  compat := by
    refine fun (i : M.ι × L.ι) (j : M.ι × L.ι) => ?_
    obtain ⟨p, q⟩ := i
    obtain ⟨p', q'⟩ := j
    have h1 : ((X.presheaf.map (homOfLE (inf_le_left :
          M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q') ≤ M.U p ⊓ L.U q)).op).hom (w.f (p, q))) ^ n =
        (((res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (M.g p p') *
          (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (L.g q q'))⁻¹ :
            Γ(X, M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q'))ˣ) : Γ(X, M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q'))) *
          (X.presheaf.map (homOfLE (inf_le_right :
            M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q') ≤ M.U p' ⊓ L.U q')).op).hom (w.f (p', q'))) ^ n :=
      congrArg (· ^ n) (w.compat (p, q) (p', q'))
    rw [mul_pow, ← Units.val_pow_eq_pow_val, ← res_pow_mul_inv] at h1
    exact (map_pow _ _ _).trans (h1.trans (congrArg _ (map_pow _ _ _).symm))

def powMod (E : X.Modules) (n : ℕ) : X.Modules := toMod (GlobalTheory.AbLaw.pw (det E 1) n)

theorem isVB_powMod {E : X.Modules} (hE : IsVB E 1) (n : ℕ) : IsVB (powMod E n) 1 :=
  GlobalTheory.VB.isVB_toMod (GlobalTheory.AbLaw.isLB_pw hE.isLB_det n)

def powHom {E E' : X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1) (ψ : E' ⟶ E) (n : ℕ) :
    powMod E' n ⟶ powMod E n :=
  homOfSec (GlobalTheory.AbLaw.isLB_pw hE'.isLB_det n) (GlobalTheory.AbLaw.isLB_pw hE.isLB_det n)
    (secPow (secOfHom hE'.isLB_det hE.isLB_det (hE'.isoDet.inv ≫ ψ ≫ hE.isoDet.hom)) n)

def frm {E : X.Modules} (hE : IsVB E 1) (n : ℕ) (c : Chart E 1) : Fin 1 → Γ(powMod E n, c.U) :=
  fun _ => GlobalTheory.LB.chartSec (GlobalTheory.AbLaw.isLB_pw hE.isLB_det n) c

theorem isFrame_frm {E : X.Modules} (hE : IsVB E 1) (n : ℕ) (c : Chart E 1) : IsFrame (frm hE n c) :=
  GlobalTheory.VB.isFrame_chartSec (GlobalTheory.AbLaw.isLB_pw hE.isLB_det n) c

theorem eq_of_smul_eq {E : X.Modules} {U V : X.Opens} {e : Fin 1 → Γ(E, U)} (he : IsFrame e)
    (h : V ≤ U) {a b : Γ(X, V)} (hab : a • resM E h (e 0) = b • resM E h (e 0)) : a = b :=
  congrFun ((he V h).1 (a₁ := fun _ => a) (a₂ := fun _ => b)
    (by simpa [Fintype.linearCombination_apply] using hab)) 0

theorem homOfSec_app_chartSec {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L))
    (p : M.ι) (q : L.ι) {V : X.Opens} (hp : V ≤ M.U p) (hq : V ≤ L.U q) :
    (homOfSec hL hM w).app V (resM _ hq (GlobalTheory.LB.chartSec hL q)) =
      resG X (le_inf hp hq) (homCoord w p q) • resM _ hp (GlobalTheory.LB.chartSec hM p) := by
  have h := GlobalTheory.LB.resG_homFun hL hM (homOfSec hL hM w) p q (le_inf hp hq)
  rw [← GlobalTheory.LB.homCoord_secOfHom, GlobalTheory.LB.secOfHom_homOfSec] at h
  rw [h]
  exact ((GlobalTheory.LB.chartEquiv hM p hp).symm_apply_apply _).symm

theorem homOfSec_secPow_app_chartSec {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L))
    (n : ℕ) (p : M.ι) (q : L.ι) {V : X.Opens} (hp : V ≤ M.U p) (hq : V ≤ L.U q) :
    (homOfSec (GlobalTheory.AbLaw.isLB_pw hL n) (GlobalTheory.AbLaw.isLB_pw hM n) (secPow w n)).app V
        (resM _ hq (GlobalTheory.LB.chartSec (GlobalTheory.AbLaw.isLB_pw hL n) q)) =
      resG X (le_inf hp hq) (homCoord w p q) ^ n • resM _ hp (GlobalTheory.LB.chartSec (GlobalTheory.AbLaw.isLB_pw hM n) p) :=
  (homOfSec_app_chartSec (GlobalTheory.AbLaw.isLB_pw hL n) (GlobalTheory.AbLaw.isLB_pw hM n) (secPow w n) p q hp hq).trans
    (congrArg (· • resM _ hp (GlobalTheory.LB.chartSec (GlobalTheory.AbLaw.isLB_pw hM n) p))
      (map_pow (resG X (le_inf hp hq)) (homCoord w p q) n))

theorem isoDet_hom_app {E : X.Modules} (hE : IsVB E 1) (c : Chart E 1) {V : X.Opens} (h : V ≤ c.U) :
    hE.isoDet.hom.app V (resM E h (c.e 0)) = resM _ h (GlobalTheory.LB.chartSec hE.isLB_det c) := by
  rw [app_resM, ← GlobalTheory.VB.wedge_frame hE c]
  exact congrArg _ (congrArg (GlobalTheory.VB.wedge E c.U 1)
    (funext fun j => congrArg c.e (Subsingleton.elim _ _)))

theorem powHom_app_frm {E E' : X.Modules} (hE : IsVB E 1) (hE' : IsVB E' 1) (ψ : E' ⟶ E) (n : ℕ)
    (c : Chart E 1) (c' : Chart E' 1) {V : X.Opens} (h : V ≤ c.U) (h' : V ≤ c'.U) {a : Γ(X, V)}
    (ha : ψ.app V (resM E' h' (c'.e 0)) = a • resM E h (c.e 0)) (i j : Fin 1) :
    (powHom hE hE' ψ n).app V (resM _ h' (frm hE' n c' i)) = a ^ n • resM _ h (frm hE n c j) := by
  have h1 := homOfSec_app_chartSec hE'.isLB_det hE.isLB_det
    (secOfHom hE'.isLB_det hE.isLB_det (hE'.isoDet.inv ≫ ψ ≫ hE.isoDet.hom)) c c' h h'
  rw [GlobalTheory.LB.homOfSec_secOfHom] at h1
  have h0 : (hE'.isoDet.inv ≫ ψ ≫ hE.isoDet.hom).app V (hE'.isoDet.hom.app V (resM E' h' (c'.e 0))) =
      a • hE.isoDet.hom.app V (resM E h (c.e 0)) := by
    rw [GlobalTheory.QCoh.app_app, Iso.hom_inv_id_assoc, ← GlobalTheory.QCoh.app_app, ha, Scheme.Modules.Hom.app_smul]
  rw [isoDet_hom_app, isoDet_hom_app] at h0
  have h2 := eq_of_smul_eq (GlobalTheory.VB.isFrame_chartSec hE.isLB_det c) h (h0.symm.trans h1)
  have h3 := homOfSec_secPow_app_chartSec hE'.isLB_det hE.isLB_det
    (secOfHom hE'.isLB_det hE.isLB_det (hE'.isoDet.inv ≫ ψ ≫ hE.isoDet.hom)) n c c' h h'
  rw [← h2] at h3
  exact h3

theorem resM_frm {E : X.Modules} (hE : IsVB E 1) (n : ℕ) (c c' : Chart E 1) {V : X.Opens}
    (h : V ≤ c.U) (h' : V ≤ c'.U) {a : Γ(X, V)} (ha : resM E h' (c'.e 0) = a • resM E h (c.e 0))
    (i j : Fin 1) : resM _ h' (frm hE n c' i) = a ^ n • resM _ h (frm hE n c j) := by
  have h1 := congrArg (hE.isoDet.hom.app V) ha
  rw [Scheme.Modules.Hom.app_smul, isoDet_hom_app, isoDet_hom_app] at h1
  have h2 := (GlobalTheory.LB.bijective_smul_chartSec hE.isLB_det c V h).1
    (h1.symm.trans (GlobalTheory.LB.map_chartSec_change hE.isLB_det c c' h h'))
  refine (GlobalTheory.LB.map_chartSec_change (GlobalTheory.AbLaw.isLB_pw hE.isLB_det n) c c' h h').trans
    (congrArg (· • _) ?_)
  rw [h2, ← map_pow, ← Units.val_pow_eq_pow_val, ← zpow_natCast]
  rfl

theorem exists_eq_smul {E : X.Modules} {U V : X.Opens} {e : Fin 1 → Γ(E, U)} (he : IsFrame e)
    (h : V ≤ U) (s : Γ(E, V)) : ∃ a : Γ(X, V), s = a • resM E h (e 0) := by
  obtain ⟨a, rfl⟩ := (he V h).2 s
  exact ⟨a 0, by simp [Fintype.linearCombination_apply]⟩

theorem hom_ext_of_frames {F G : X.Modules} {φ ψ : F ⟶ G} {ι : Type} [Fintype ι]
    (h : ∀ x : X, ∃ (U : X.Opens) (e : ι → Γ(F, U)), x ∈ U ∧ IsFrame e ∧
      ∀ i, φ.app U (e i) = ψ.app U (e i)) : φ = ψ := by
  choose U e hx he h using h
  have hU : ⨆ x, U x = ⊤ := top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩
  ext V s : 3
  refine GlobalTheory.Twist.sec_ext_of_cover (fun x => V ⊓ U x) (fun _ => inf_le_left)
    (GlobalTheory.LB.le_iSup_inf hU V) fun x => ?_
  rw [← app_resM, ← app_resM]
  obtain ⟨a, ha⟩ := (he x _ (inf_le_right : V ⊓ U x ≤ U x)).2 (resM F inf_le_left s)
  rw [← ha]
  simp only [Fintype.linearCombination_apply, map_sum, Scheme.Modules.Hom.app_smul, app_resM, h]

theorem exists_iso_of_frames {F G : X.Modules} {κ : Type} {U : κ → X.Opens} (hU : ⨆ k, U k = ⊤)
    {e : ∀ k, Fin 1 → Γ(F, U k)} {f : ∀ k, Fin 1 → Γ(G, U k)} (he : ∀ k, IsFrame (e k))
    (hf : ∀ k, IsFrame (f k))
    (h : ∀ k l, ∃ a : Γ(X, U k ⊓ U l), resM F inf_le_right (e l 0) = a • resM F inf_le_left (e k 0) ∧
      resM G inf_le_right (f l 0) = a • resM G inf_le_left (f k 0)) :
    ∃ θ : F ≅ G, ∀ k i, θ.hom.app (U k) (e k i) = f k i := by
  have key (k l : κ) {V : X.Opens} (hk : V ≤ U k) (hl : V ≤ U l) (s : Γ(F, V)) :
      (he k).equiv (hf k) hk s = (he l).equiv (hf l) hl s := by
    obtain ⟨b, rfl⟩ := exists_eq_smul (he l) hl s
    obtain ⟨a, h₁, h₂⟩ := h k l
    have h₁' := congrArg (resM F (le_inf hk hl)) h₁
    have h₂' := congrArg (resM G (le_inf hk hl)) h₂
    rw [resM_smul, resM_resM, resM_resM] at h₁' h₂'
    rw [map_smul, map_smul, IsFrame.equiv_resM_frame, h₁', map_smul, IsFrame.equiv_resM_frame, h₂']
  have H (V : X.Opens) (s : Γ(F, V)) : ∃ t : Γ(G, V), ∀ k,
      resM G inf_le_left t = (he k).equiv (hf k) (inf_le_right : V ⊓ U k ≤ U k) (resM F inf_le_left s) :=
    GlobalTheory.Twist.exists_sec_of_cover (fun k => V ⊓ U k) (fun _ => inf_le_left) (GlobalTheory.LB.le_iSup_inf hU V) _
      fun k l => by
        rw [← IsFrame.equiv_resM, ← IsFrame.equiv_resM, resM_resM, resM_resM]
        exact key k l _ _ _
  choose t ht using H
  have ext {V : X.Opens} {a b : Γ(G, V)}
      (e : ∀ k, resM G (inf_le_left : V ⊓ U k ≤ V) a = resM G inf_le_left b) : a = b :=
    GlobalTheory.Twist.sec_ext_of_cover (fun k => V ⊓ U k) (fun _ => inf_le_left) (GlobalTheory.LB.le_iSup_inf hU V) e
  have ht' (V : X.Opens) (s : Γ(F, V)) (k : κ) (W : X.Opens) (h₁ : W ≤ V) (h₂ : W ≤ U k) :
      resM G h₁ (t V s) = (he k).equiv (hf k) h₂ (resM F h₁ s) := by
    have := congrArg (resM G (le_inf h₁ h₂)) (ht V s k)
    rwa [← IsFrame.equiv_resM, resM_resM, resM_resM] at this
  let θ : F ⟶ G := GlobalTheory.LB.homOfLinear (fun V =>
    { toFun := t V
      map_add' := fun a b => ext fun k => by simp only [map_add, ht]
      map_smul' := fun a b => ext fun k => by simp only [resM_smul, ht, map_smul, RingHom.id_apply] })
    fun {V W} hW s => ext fun k => by
      change resM G _ (t W (resM F hW s)) = resM G _ (resM G hW (t V s))
      rw [ht, resM_resM, resM_resM, ht' V s k _ _ inf_le_right]
  have hθ (k : κ) (i : Fin 1) : θ.app (U k) (e k i) = f k i := by
    have := ht' (U k) (e k i) k (U k) le_rfl le_rfl
    rwa [IsFrame.equiv_resM_frame, GlobalTheory.Twist.resM_self, GlobalTheory.Twist.resM_self] at this
  haveI : IsIso θ := GlobalTheory.VB.isIso_of_frames θ fun x => by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU.ge (TopologicalSpace.Opens.mem_top x))
    exact ⟨U k, e k, hk, he k, by rw [funext (hθ k)]; exact hf k⟩
  exact ⟨asIso θ, hθ⟩

end GlobalTheory.LinePow
