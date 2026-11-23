import Formalism.SharpRestriction.GrowthBounds.ChartComparison.KerLabelsMu
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.CmpJMemSpan
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.IntAtJIffN
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.HtupWLeHtupJ
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.TwPinned

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms NumberField

theorem locW_map {LL : Type} [Field LL] [NumberField LL] (Pl : Rows.Places LL) (w : Pl.Pl) {V V' : Type} [AddCommGroup V] [Module LL V]
    [Module (𝓞 LL) V] [AddCommGroup V'] [Module LL V'] [Module (𝓞 LL) V'] (ε : V →ₗ[LL] V') (L : Submodule (𝓞 LL) V)
    (L' : Submodule (𝓞 LL) V') (h : ∀ x, x ∈ L → ε x ∈ L') (x : V) (hx : x ∈ Formalism.BasicNotions.locW Pl w L) :
    ε x ∈ Formalism.BasicNotions.locW Pl w L' := by
  unfold Formalism.BasicNotions.locW at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (h y hy)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
  | smul a y _ h1 =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ _ h1

theorem locW_equiv {LL : Type} [Field LL] [NumberField LL] (Pl : Rows.Places LL) (w : Pl.Pl) {V V' : Type} [AddCommGroup V] [Module LL V]
    [Module (𝓞 LL) V] [AddCommGroup V'] [Module LL V'] [Module (𝓞 LL) V'] (ε : V ≃ₗ[LL] V') (L : Submodule (𝓞 LL) V)
    (L' : Submodule (𝓞 LL) V') (h : ∀ x, x ∈ L ↔ ε x ∈ L') (y : V') :
    ε.symm y ∈ Formalism.BasicNotions.locW Pl w L ↔ y ∈ Formalism.BasicNotions.locW Pl w L' := by
  constructor
  · intro hy
    have := locW_map Pl w ε.toLinearMap L L' (fun x hx => (h x).1 hx) _ hy
    rwa [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
  · intro hy
    exact locW_map Pl w ε.symm.toLinearMap L' L (fun x hx => (h _).2 (by rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]; exact hx)) _ hy

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure StepAt (j : ℕ) (hj : j + 1 ≤ D.R.m) where
  C : ColumnChain D.R D.what₂.Tau (D.hcW u)
  A : ColumnsAtT D.R C
  P : PeriodMap D.R C
  M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P
  eps : (M.lat (j + 1)).V ≃ₗ[D.what₂.LL] ((Tw.fm u μ).lat (j + 1)).V
  eps_lat : ∀ x, x ∈ (M.lat (j + 1)).L ↔ eps x ∈ ((Tw.fm u μ).lat (j + 1)).L
  eps_emb : ∀ x, HEq ((Tw.fm u μ).emb (j + 1) (eps x)) (M.emb (j + 1) x)
  st : StepIn M (j + 1) hj (gatJ Lv (j + 1))

variable {Tw u μ w h Lv}

def StepAt.ofTw {j : ℕ} {hj : j + 1 ≤ D.R.m} (st : StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1))) : StepAt Tw u μ w h Lv j hj where
  C := D.chTw u μ
  A := Tw.A u μ
  P := D.PTw u μ
  M := Tw.fm u μ
  eps := LinearEquiv.refl _ _
  eps_lat := fun _ => Iff.rfl
  eps_emb := fun _ => HEq.rfl
  st := st

def StepAt.ofMem {j : ℕ} {hj : j + 1 ≤ D.R.m} (st : StepIn (D.fm u) (j + 1) hj (gatJ Lv (j + 1))) :
    StepAt Tw u D.what₂.mu0 w h Lv j hj where
  C := (D.mem u).C
  A := (D.mem u).A
  P := (D.mem u).P
  M := D.fm u
  eps := Tw.eMu0 u (j + 1) hj
  eps_lat := Tw.eMu0_lat u (j + 1) hj
  eps_emb := Tw.eMu0_emb u (j + 1) hj
  st := st

variable (Tw u μ w h Lv)

structure CmpJIn where
  at' : ∀ j (hj : j + 1 ≤ D.R.m), StepAt Tw u μ w h Lv j hj

variable {Tw u μ w h Lv}

def CmpJIn.Pinned (Hh : Formalism.L2.Herm.HermTied D) (I : CmpJIn Tw u μ w h Lv) : Prop := ∀ j hj, (I.at' j hj).st.TwPinned Hh

structure CmpJHyp (I : CmpJIn Tw u μ w h Lv) : Prop where

  core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β

  ok : ∀ j hj, (I.at' j hj).st.okW w

  twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β

  valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w

  iwF : ∀ j hj β, (I.at' j hj).st.IwF β

  fin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses

  card : ∀ j hj, Fintype.card ((I.at' j hj).M.lat (j + 1)).ι = Module.finrank (D.gat u w h).O (gatJ Lv (j + 1)).M

variable {c}

def plc (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Fin (D.gat u w h).P.nV := ⟨0, Formalism.MainNotions.G.Inhab.gatHasPlaces_of_ties Gt u w h⟩

theorem CmpJHyp.valInt {I : CmpJIn Tw u μ w h Lv} (H : CmpJHyp c I) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    (I.at' j hj).st.ValIntJ (c.embW u w h) w :=
  StepIn.valIntJ_of (S := (I.at' j hj).st) (c.embW u w h) w (H.twUnit j hj) (H.valIntN j hj)

open Classical in

def cmpSJ {I : CmpJIn Tw u μ w h Lv} (H : CmpJHyp c I) (hS : BlockRationalityField) (j : ℕ) :
    ((Tw.fm u μ).lat (j + 1)).V →ₛₗ[c.embW u w h] Lv.Fm (j + 1) :=
  if hj : j + 1 ≤ D.R.m then
    (StepIn.cmpJL (S := (I.at' j hj).st) (c.embW u w h) (H.core j hj) hS).comp (I.at' j hj).eps.symm.toLinearMap
  else 0

theorem cmpSJ_apply {I : CmpJIn Tw u μ w h Lv} (H : CmpJHyp c I) (hS : BlockRationalityField) (j : ℕ) (hj : j + 1 ≤ D.R.m)
    (x : ((Tw.fm u μ).lat (j + 1)).V) :
    cmpSJ H hS j x = (I.at' j hj).st.cmpJ (c.embW u w h) ((I.at' j hj).eps.symm x) := by
  unfold cmpSJ
  rw [dif_pos hj]
  rfl

theorem descUp {I : CmpJIn Tw u μ w h Lv} (H : CmpJHyp c I) (Gt : GatTies D) : DescUp c u w h Lv := by
  intro j hj
  have : IsFractionRing (gatJ Lv (j + 1)).O (gatJ Lv (j + 1)).Kf := ((D.gat u w h).P.setting (plc Gt u w h)).frac_O
  exact StepIn.desc (S := (I.at' j hj).st) (c.embW u w h) (H.core j hj) (H.iwF j hj) (D.plEq w)
    (fun x => (D.val_nonneg_iff w x).symm.trans (c.embW_int u w h x)) (H.fin j hj)

def stepsMu {I : CmpJIn Tw u μ w h Lv} (H : CmpJHyp c I) (hS : BlockRationalityField) (Gt : GatTies D) :
    StepsMu c Tw u μ w h Lv where
  cmpS := cmpSJ H hS
  injS := fun j hj x y hxy => (I.at' j hj).eps.symm.injective
    (StepIn.cmpJ_inj (S := (I.at' j hj).st) (c.embW u w h) (H.core j hj) hS (by
      rw [StepIn.cmpJL_apply, StepIn.cmpJL_apply, ← cmpSJ_apply H hS j hj, ← cmpSJ_apply H hS j hj]
      exact hxy))
  ratS := fun j hj x => by
    rw [cmpSJ_apply H hS j hj]
    exact StepIn.cmpJ_rat (S := (I.at' j hj).st) (c.embW u w h) _
  latS := fun j hj x => by
    rw [cmpSJ_apply H hS j hj]
    exact (StepIn.cmpJ_lat (S := (I.at' j hj).st) (c.embW u w h) (H.core j hj) hS w (H.ok j hj) (H.valInt j hj) _).trans
      (locW_equiv D.what₂.places w (I.at' j hj).eps _ _ (I.at' j hj).eps_lat x)
  surjS := fun j hj F hF hr => by
    have : IsFractionRing (gatJ Lv (j + 1)).O (gatJ Lv (j + 1)).Kf := ((D.gat u w h).P.setting (plc Gt u w h)).frac_O
    have : Module.Finite (gatJ Lv (j + 1)).O (gatJ Lv (j + 1)).M := mfin_of Gt u w h Lv (j + 1) (H.fin j hj)
    obtain ⟨x, hx⟩ := StepIn.surj_of_card (S := (I.at' j hj).st) (c.embW u w h) (H.core j hj) hS w (H.ok j hj) (H.valInt j hj)
      (H.card j hj) F hF hr
    exact ⟨(I.at' j hj).eps x, by rw [cmpSJ_apply H hS j hj, LinearEquiv.symm_apply_apply, hx]⟩

def kerAtMu_cmpJ (K : KerLabelsMu Tw u μ w h Lv) {I : CmpJIn Tw u μ w h Lv} (H : CmpJHyp c I) (hS : BlockRationalityField)
    (Gt : GatTies D) : TwTie.KerAtMu D c Tw u μ w h (chainMu (stepsMu H hS Gt).up) :=
  kerAtMu K (stepsMu H hS Gt) (descUp H Gt) (plc Gt u w h)

theorem kerAtMu_cmpJ_cmp (K : KerLabelsMu Tw u μ w h Lv) {I : CmpJIn Tw u μ w h Lv} (H : CmpJHyp c I) (hS : BlockRationalityField)
    (Gt : GatTies D) (j : ℕ) (hj : j + 1 ≤ D.R.m) (x : ((Tw.fm u μ).lat (j + 1)).V) :
    (kerAtMu_cmpJ K H hS Gt).cmp (j + 1) x = (I.at' j hj).st.cmpJ (c.embW u w h) ((I.at' j hj).eps.symm x) :=
  cmpSJ_apply H hS j hj x

def kerAtMu_any (K : KerLabelsMu Tw u μ w h Lv) {I : CmpJIn Tw u μ w h Lv} (H : CmpJHyp c I) (hS : BlockRationalityField)
    (Gt : GatTies D) (Ch : Chain Lv)
    (hCh : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u μ).lat j).V) (y : ((Tw.fm u μ).lat (j + 1)).V),
      (Tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((Tw.fm u μ).emb j x) →
      (stepsMu H hS Gt).up.cmp (j + 1) y = Ch.Kz j ((stepsMu H hS Gt).up.cmp j x)) :
    TwTie.KerAtMu D c Tw u μ w h Ch where
  fl_t := K.fl_t
  fl_m := K.fl_m
  cls := K.cls
  cls_iff := K.cls_iff
  cls_surj := K.cls_surj
  stab_zero := K.stab_zero
  stab_dvd := K.stab_dvd
  cmp := (kerAtMu_cmpJ K H hS Gt).cmp
  cmp_inj := (kerAtMu_cmpJ K H hS Gt).cmp_inj
  cmp_zero := (kerAtMu_cmpJ K H hS Gt).cmp_zero
  cmp_int := (kerAtMu_cmpJ K H hS Gt).cmp_int
  cmp_K := hCh
  rat := K.rat
  val := (kerAtMu_cmpJ K H hS Gt).val

structure TieAt (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
    (hS : BlockRationalityField) (Gt : GatTies D) where
  lab : KerLabelsMu Tw u μ w h Lv
  inp : CmpJIn Tw u μ w h Lv
  hyp : CmpJHyp c inp
  ch : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u μ).lat j).V) (y : ((Tw.fm u μ).lat (j + 1)).V),
      (Tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((Tw.fm u μ).emb j x) →
      (stepsMu hyp hS Gt).up.cmp (j + 1) y = Ch.Kz j ((stepsMu hyp hS Gt).up.cmp j x)

def twistCompatibleAt_of_localCompatibility {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Dx : DivX D} {cX : ExtraC}
    (E : Extra D L hT Gi Gl K Dx cX)
    (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      Σ Lv : Levels (Gl.Fl u w hg), Chain Lv) (hS : BlockRationalityField)
    (t : ∀ (μ : D.what₂.Tup), DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      D.what₂.places.resChar w ∉ Dx.Qp μ → TieAt E.cmp E.tw u μ w h (((Pk.reW Gl LC).Yt μ).Ch u w h) hS hT)
    (e0 : ∀ u, E.tw.e0 u D.what₂.mu0 = E.tw.eMu0 u 0 (Nat.zero_le _)) : TwTie.TwistedUnitaryExtraData E where
  LC := LC
  ker := fun μ hU u w h hq => kerAtMu_any (t μ hU u w h hq).lab (t μ hU u w h hq).hyp hS hT _ (t μ hU u w h hq).ch
  twisted_e0_at_mu0_eq_eMu0 := e0

end Formalism.MainNotions.G.CmpJ

end
