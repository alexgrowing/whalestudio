import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CmpCMemMIff
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ExistsPrimeToLe
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfRatInv
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfWeak
import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IsUnitDetBlockPreimage
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtRec

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

structure CmpCore (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop where

  same : ∀ u, SameUloc X T u

  ex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  pos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
      (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x))

  chi : ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

variable {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X}

set_option maxHeartbeats 1000000 in

theorem cmpRec_lat_pf (H : CmpCore T Gt I) (hloc : ValIntRec T Gt I)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (x : ((D.fm u).lat 0).V) :
    cmpRec T Gt I u w hg x ∈ (D.gat u w hg).M ↔ x ∈ locW D.what₂.places w ((D.fm u).lat 0).L := by
  rw [locWCrit_proved T u w x]
  exact cmpC_mem_M_iff (tEL D) (tEL_emb D) (embT_conj D) (locAt_std u w hg I.B I.B_std)
    (locAt_actB u w hg I.B (I.fr_B u w hg)) (H.ex u w hg)
    (H.pos u w hg) (H.chi u w hg) (evInj_rec Gt I u w hg) (ptEx_rec X T u w hg I.B) (ptAll_rec X T u (H.same u) w hg I.B)
    (locAt_UJ u w hg I.B) (awayEx_rec X T u (H.same u) w hg I.B) (IntAtW T u w) (hloc u w hg) x

def SurjRat (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop :=
  ∀ u w hg, ∀ F ∈ (D.gat u w hg).M, RatFn (D.gat u w hg) (I.embW u w hg) F → ∃ x, cmpRec T Gt I u w hg x = F

set_option maxHeartbeats 1000000 in

theorem latM_pf (H : CmpCore T Gt I) (hloc : ValIntRec T Gt I) (hsurj : SurjRat T Gt I)
    (hd : ∀ u w hg, MRatSpan (D.gat u w hg).P (D.gat u w hg).comp (I.embW u w hg) (D.gat u w hg).M)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule.span (D.gat u w hg).O
      (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M :=
  span_image_of_surj (D.gat u w hg).P (D.gat u w hg).comp (I.embW u w hg) (D.gat u w hg).M
    (cmpL (e := I.embW u w hg) (H.ex u w hg) (valUniq_of (embT_conj D) (evInj_rec Gt I u w hg) (ptEx_rec X T u w hg I.B)))
    (intW D.what₂.places w) (fun a ha => (I.embW_int u w hg a).1 ha) _ (hsurj u w hg)
    (fun x => cmpRec_lat_pf H hloc u w hg x) (hd u w hg)

theorem posCompat_rec (H : CmpCore T Gt I) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    PosCompat (D.gat u w hg) (I.embW u w hg) (locAt X u w hg I.B).iw
      (fun v s => tPos (sigD D) (tEL D) (Gt.gat_pos u w hg) v s) := by
  intro v s x
  rw [tPos_apply]
  exact H.pos u w hg v s x

theorem actE_rec (I : CmpIn D X) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ActE (D.gat u w hg) (locAt X u w hg I.B).iw := by
  intro i γ
  refine ⟨(castGL (locAt X u w hg I.B).rk D.host.E).symm
    ((locAt X u w hg I.B).B⁻¹ * (locAt X u w hg I.B).gamI i γ * (locAt X u w hg I.B).B), fun v => ?_⟩
  have hA := locAt_actB u w hg I.B (I.fr_B u w hg)
  have h1 : ((D.gat u w hg).lev i).act v γ = bc ((locAt X u w hg I.B).iw v)
      ((castGL (locAt X u w hg I.B).rk D.host.E).symm
        ((locAt X u w hg I.B).B⁻¹ * (locAt X u w hg I.B).gamI i γ * (locAt X u w hg I.B).B)) := by
    rw [← castGL_symm_bc, ← hA i v γ, MulEquiv.symm_apply_apply]
  rw [h1]
  apply Units.ext
  ext a b
  rfl

theorem chiRat_rec (H : CmpCore T Gt I) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : ChiRat (D.gat u w hg) (I.embW u w hg) := by
  intro i γ
  obtain ⟨κ, hκ⟩ := awayEx_rec X T u (H.same u) w hg I.B i γ
  obtain ⟨r, _, hr⟩ := H.chi u w hg i γ κ hκ
  exact ⟨r⁻¹, by rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_left hr).symm⟩

theorem mRatSpan_rec (H : CmpCore T Gt I) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (hfrac : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf) (hfin : (D.gat u w hg).FinClasses)
    (hw : WeakApprox (D.gat u w hg) (locAt X u w hg I.B).iw) :
    MRatSpan (D.gat u w hg).P (D.gat u w hg).comp (I.embW u w hg) (D.gat u w hg).M :=
  mRatSpan_of_rat_inv (D.gat u w hg) (I.embW u w hg) (D.plEq w)
    (fun x => (val_nonneg_iff D w x).symm.trans (I.embW_int u w hg x)) hfin
    (ratLev_of (D.gat u w hg) (I.embW u w hg) (locAt X u w hg I.B).iw _ (posCompat_rec H u w hg) (actE_rec I u w hg)
      (chiRat_rec H u w hg))
    (ratBasis_of (D.gat u w hg) (I.embW u w hg) (locAt X u w hg I.B).iw _ (posCompat_rec H u w hg)
      (ratTup_of_weak (D.gat u w hg) (locAt X u w hg I.B).iw hw))

theorem finClasses_of_gatIs (Hm : LevelData D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (h : GatIs D Hm u w hg) : (D.gat u w hg).FinClasses := by
  obtain ⟨W, Qq, O, Kf, _, _, _, _, _, _, _, _, _, _, n', ι, σ, j, w0, hS, nV, r, m, lam0, dom, hk, I, ψ, e, hH, heq⟩ := h
  rw [heq]
  exact Cmp.finClasses hS r lam0 dom hk I ψ e (isUnit_det_gram0 D.sp) hH

theorem frac_of_gatIs (Hm : LevelData D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (h : GatIs D Hm u w hg) :
    IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf := by
  obtain ⟨W, Qq, O, Kf, _, _, _, _, _, _, _, _, _, _, n', ι, σ, j, w0, hS, nV, r, m, lam0, dom, hk, I, ψ, e, hH, heq⟩ := h
  rw [heq]
  exact hS.frac_O

def WeakRec (I : CmpIn D X) : Prop :=
  ∀ u w hg, WeakApprox (D.gat u w hg) (locAt X u w hg I.B).iw

theorem latM_rec (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I)
    (hsurj : SurjRat T Gt I) (hw : WeakRec I)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule.span (D.gat u w hg).O
      (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M :=
  latM_pf H hloc hsurj (fun u w hg => mRatSpan_rec H u w hg (frac_of_gatIs X.lev0 u w hg (hG u w hg))
    (finClasses_of_gatIs X.lev0 u w hg (hG u w hg)) (hw u w hg)) u w hg

end Formalism.L2.G
