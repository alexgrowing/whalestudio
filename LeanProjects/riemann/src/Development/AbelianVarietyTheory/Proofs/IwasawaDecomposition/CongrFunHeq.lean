import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D)

def Mv.lam (x : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat m.D := @_root_.GlobalTheory.LamTie.LamDat.mk (_)
    (C := @_root_.Formalism.L2.Host.CharFrame.mk (_)
      (P := (by with_unfolding_all exact (x.C.P :)))
      (W := (by with_unfolding_all exact (x.C.W :)))
      (mu0 := (by with_unfolding_all exact (x.C.mu0 :)))
      (eta := (by with_unfolding_all exact (x.C.eta :)))
      (chiPsi := (by with_unfolding_all exact (x.C.chiPsi :)))
      (del := (by with_unfolding_all exact (x.C.del :)))
      (del' := (by with_unfolding_all exact (x.C.del' :)))
      (isMu0 := (by with_unfolding_all exact (x.C.isMu0 :)))
      (isEta := (by with_unfolding_all exact (x.C.isEta :)))
      (isChi := (by with_unfolding_all exact (x.C.isChi :)))
      (isDel := (by with_unfolding_all exact (x.C.isDel :)))
      (isDel' := (by with_unfolding_all exact (x.C.isDel' :))))
    (q0 := (by with_unfolding_all exact (x.q0 :)))
    (w0 := (by with_unfolding_all exact (x.w0 :)))
    (c := (by with_unfolding_all exact (x.c :)))
    (chi := (by with_unfolding_all exact (x.chi :)))
theorem Mv.lam_ok {l : GlobalTheory.LamTie.LamDat D} (x : l.Ok) : (m.lam l).Ok := @_root_.GlobalTheory.LamTie.LamDat.Ok.mk (_) (_)
    (places := (by with_unfolding_all exact (x.places :)))
    (aux := (by with_unfolding_all exact (x.aux :)))
    (big := (by with_unfolding_all exact (x.big :)))
theorem Mv.lam_teich {l : GlobalTheory.LamTie.LamDat D} (x : l.Teich) : (m.lam l).Teich := (by with_unfolding_all exact (x :))
theorem Mv.lam_tie {l : GlobalTheory.LamTie.LamDat D} (x : GlobalTheory.LamTie.IsLamTieFull D.ntw l) : GlobalTheory.LamTie.IsLamTieFull m.D.ntw (m.lam l) := (by with_unfolding_all exact (x :))

theorem Mv.rowLoc {D : D7} (m : Mv D) {C : NChoice D} (a : NAllC D C) (F : Formalism.L2.RowFrame D) (F' : Formalism.L2.RowFrame m.D)
    (hF : HEq F'.rep F.rep) (x : Formalism.L2.RowLocTied D a.gal.lp F) : Formalism.L2.RowLocTied m.D (m.all a).gal.lp F' := by
  obtain ⟨rep, inj⟩ := F
  obtain ⟨rep', inj'⟩ := F'
  have e : rep' = (by with_unfolding_all exact (rep :)) := eq_of_heq ((by with_unfolding_all exact (hF :)))
  subst e
  exact (@_root_.Formalism.L2.RowLocTied.mk (_) (_) (_)
    (sat := (by with_unfolding_all exact (x.sat :)))
    )

theorem congrFun_heq {α β : Type} {f g : α → β} (h : HEq f g) (x : α) : f x = g x := by rw [eq_of_heq h]

theorem exists_row (hL : GlobalTheory.Published.LocalLanglandsGL) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z))
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0')
    (hs : RowsSame t t') (hg : HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo))
    (hj : ∀ (μ : (w.D Z).what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ) (hμ' : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ) (i : Fin (w.D Z).R.m) (x : (w.D Z).what₂.Mt μ ((i : ℕ) + 1)), HEq (t'.r.Y.IL.jMt μ hμ' i x).1 (t.r.Y.IL.jMt μ hμ i x).1)
    (hser : ∀ (kKs : ↥t.r.z.core.Q.c.F →+* ↥(w.st Z).toD7.LL0) (hk : ∀ x, ((kKs x : ↥(w.st Z).toD7.LL0) : (w.st Z).toD7.what₂.LL) = algebraMap _ (w.st Z).toD7.what₂.LL x) (YS : Formalism.IndefR.NX.NExpRealS t.r.z.R t.r.z.cG (Formalism.IndefR.NX.ratDatR t.r.z.R t.r.z.cG kKs hk)) (kKs' : ↥t'.r.z.core.Q.c.F →+* ↥(w.st (upL Z S' N h)).toD7.LL0) (hk' : ∀ x, ((kKs' x : ↥(w.st (upL Z S' N h)).toD7.LL0) : (w.st (upL Z S' N h)).toD7.what₂.LL) = algebraMap _ (w.st (upL Z S' N h)).toD7.what₂.LL x) (YS' : Formalism.IndefR.NX.NExpRealS t'.r.z.R t'.r.z.cG (Formalism.IndefR.NX.ratDatR t'.r.z.R t'.r.z.cG kKs' hk')), HEq kKs' kKs → HEq YS'.fi YS.fi → HEq YS'.eF YS.eF → ∀ (a : NAllC (w.D Z) nch) (X' : Formalism.L2.NExpTied (w.st (upL Z S' N h)).toD7), HEq X' ((mvOf w Z S' N h).all a).exp → ∀ (PV : ∀ i : Fin (w.st Z).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV) (PV' : ∀ i : Fin (w.st (upL Z S' N h)).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (upL Z S' N h)).toD7 i) (w.st (upL Z S' N h)).toD7.R.nV), HEq (fun i => (PV' i).ψ) (fun i => (PV i).ψ) → ∀ Pq Pq', HEq Pq' Pq → SerAt (D := (w.st Z).toD7) YS t.r.z.geo.v₀ a.exp PV (TC.cf w.I w.l Z) Pq → Nonempty (SerAt (D := (w.st (upL Z S' N h)).toD7) YS' t'.r.z.geo.v₀ X' PV' (TC.cf w.I w.l (upL Z S' N h)) Pq'))
    {tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch} {tp' : TupTied (w.D (upL Z S' N h)) (TC.cf w.I w.l (upL Z S' N h)) (nchUp S' N h nch)}
    (a : NAt hL (w.D Z) (TC.cf w.I w.l Z) nch tp)
    (a' : NAt hL (w.D (upL Z S' N h)) (TC.cf w.I w.l (upL Z S' N h)) (nchUp S' N h nch) tp') (hA : AtSame (mvOf w Z S' N h) a a')
    (r : NRow (D := (w.st Z).toD7) a t.r.z.R t.r.z.F t.r.z.cG t.r.Y) (e : NMore (D := (w.st Z).toD7) r t.r.z.geo xd) :
    ∃ r' : NRow (D := (w.st (upL Z S' N h)).toD7) a' t'.r.z.R t'.r.z.F t'.r.z.cG t'.r.Y,
      Nonempty (NMore (D := (w.st (upL Z S' N h)).toD7) r' t'.r.z.geo (xdUp S' N h xd)) := by
  cases t' with | mk hX' r' exAt' inGeo' grpAt' grp' mu' exact' untw' emt0' emt' etaF' rowInt' idx' => ?_
  cases r' with | mk z' holds' Y' ZZ' tupix' => ?_
  cases z' with | mk Xg' tr' core' alg_eq' R' cG' geo' pins' lev' idG' good' muz' le' ks' => ?_
  rename_i alg'
  have e1 : Xg' = t.r.z.Xg := hs.Xg
  have e2 : tr' = t.r.z.tr := hs.tr
  subst e1 e2
  have e3 : core' = R3.Tr.coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) t.r.z.core := eq_of_heq hs.core
  subst e3
  have e4 : alg' = t.r.z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.D Z).what₂.embLL.injective
    exact (alg_eq' y).trans (t.r.z.alg_eq y).symm
  subst e4
  have e5 : R' = R3.Tr.real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.R := eq_of_heq hs.R
  subst e5
  have e6 : cG' = t.r.z.cG := eq_of_heq hs.cG
  subst e6
  have e7 : geo' = (by with_unfolding_all exact ((R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) :)) := eq_of_heq ((by with_unfolding_all exact (hg :)))
  subst e7
  obtain ⟨nt', all', chr_eq', host', frameN', chrN', chrGal', Pq', Pq_over', pq', jE_eq', mt_eq', Pq_eq', hlow', split', ratIn',
    r1', r2', r3', depth'⟩ := a'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hA
  have e8 : all' = (by with_unfolding_all exact (((mvOf w Z S' N h).all a.all) :)) := eq_of_heq ((by with_unfolding_all exact (s1 :)))
  have e9 : Pq' = (by with_unfolding_all exact (a.Pq :)) := eq_of_heq ((by with_unfolding_all exact (s2 :)))
  subst e8 e9
  obtain ⟨kKs, hk, nexp, hecke, grp, rowLoc, S_eq, hL_eq, rep_eq⟩ := r
  obtain ⟨ad, fi, hrow, cHk, eig, ser, tau, geo, ok, th, xda, large, labc, zeta, pht⟩ := e
  obtain ⟨geo⟩ := geo
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, IL', _, _, _, eFT', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨eW', _⟩, _⟩ := Y'
  have e10 : eW' = (by with_unfolding_all exact (t.r.Y.mj.eW :)) := eq_of_heq ((by with_unfolding_all exact (hs.eW :)))
  subst e10
  obtain ⟨Sb, ev, hSb, hev, hE⟩ := eig
  obtain ⟨i1, i2, i3⟩ := s7 ⟨labc, zeta, pht⟩
  obtain ⟨l1, l2, l3, l4, l5, lv⟩ := grp.lvl
  refine Nonempty.elim (hser kKs hk nexp ((by with_unfolding_all exact (kKs :))) ((by with_unfolding_all exact (hk :))) (@_root_.Formalism.IndefR.NX.NExpRealS.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (fi := (by with_unfolding_all exact (nexp.fi :)))
    (geq := (by with_unfolding_all exact (nexp.geq :)))
    (rho := (by with_unfolding_all exact (nexp.rho :)))
    (chi := (by with_unfolding_all exact (nexp.chi :)))
    (eF := (by with_unfolding_all exact (nexp.eF :)))
    (bsup := kc% nexp.bsup)
    (act := kc% nexp.act)
    )
    ((by with_unfolding_all exact ((HEq.refl kKs) :))) ((by with_unfolding_all exact ((HEq.refl nexp.fi) :))) ((by with_unfolding_all exact ((HEq.refl nexp.eF) :))) a.all ((by with_unfolding_all exact (((mvOf w Z S' N h).all a.all).exp :)))
    ((by with_unfolding_all exact ((HEq.refl ((mvOf w Z S' N h).all a.all).exp) :))) ad.PV (@fun x1 => @_root_.Formalism.IndefR.principalLevelFrame.RowPsi.mk (_) (_) (_)
      (ψ := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).ψ : _)))
      (inj := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).inj : _)))
      (into := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).into : _)))
      (onto := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).onto : _))))
    ((by with_unfolding_all exact ((HEq.refl fun i => (ad.PV i).ψ) :))) a.Pq ((by with_unfolding_all exact (a.Pq :))) ((by with_unfolding_all exact ((HEq.refl a.Pq) :))) ser) fun ser' => ?_
  refine ⟨@NRow.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ((by with_unfolding_all exact (kKs :))) ((by with_unfolding_all exact (hk :)))
    (@_root_.Formalism.IndefR.NX.NExpRealS.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (fi := (by with_unfolding_all exact (nexp.fi :)))
    (geq := (by with_unfolding_all exact (nexp.geq :)))
    (rho := (by with_unfolding_all exact (nexp.rho :)))
    (chi := (by with_unfolding_all exact (nexp.chi :)))
    (eF := (by with_unfolding_all exact (nexp.eF :)))
    (bsup := kc% nexp.bsup)
    (act := kc% nexp.act)
    )
    (@_root_.Formalism.IndefR.NX.NExpRealH.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (hL := (by with_unfolding_all exact (hecke.hL :)))
    (hs := (by with_unfolding_all exact (hecke.hs :)))
    (cHk := (by with_unfolding_all exact (hecke.cHk :)))
    (cHk_zero := (by with_unfolding_all exact (hecke.cHk_zero :)))
    (cHk_unit := (by with_unfolding_all exact (hecke.cHk_unit :)))
    (cHk_pow := (by with_unfolding_all exact (hecke.cHk_pow :)))
    (hkEq := kc% hecke.hkEq)
    )
    (@_root_.Formalism.L2.DIV.GrpTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (card := (by with_unfolding_all exact (grp.card :)))
    (e0 := (by with_unfolding_all exact (grp.e0 :)))
    (lvl0 := (by with_unfolding_all exact (grp.lvl0 :)))
    (psi0 := (by with_unfolding_all exact (grp.psi0 :)))
    (idxSharp := (by with_unfolding_all exact (grp.idxSharp :)))
    (lvl := ⟨(by with_unfolding_all exact (l1 :)), (by with_unfolding_all exact (l2 :)), (by with_unfolding_all exact (l3 :)), (by with_unfolding_all exact (l4 :)), (by with_unfolding_all exact (l5 :)),
      ⟨(by with_unfolding_all exact (lv.place :)), (by with_unfolding_all exact (lv.comp :)), (by with_unfolding_all exact (lv.gen :)), (by with_unfolding_all exact (lv.p0 :)), (by with_unfolding_all exact (lv.chi0 :)), (by with_unfolding_all exact (lv.ps :)), (by with_unfolding_all exact (lv.chis :))⟩⟩)
    )
    ((by with_unfolding_all exact (((mvOf w Z S' N h).rowLoc a.all _ (kc% (Formalism.L2.Col.rowFrameOf (w.D (upL Z S' N h)) _ eFT')) (kc% hs.rep) rowLoc) :)))
    (kc% (s3.trans S_eq)) (kc% (s4.trans hL_eq)) (kc% ((s5.trans rep_eq).trans hs.rep.symm)), ⟨@NMore.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (@_root_.GlobalTheory.HeightCounting.MtAd.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (PV := @fun x1 => @_root_.Formalism.IndefR.principalLevelFrame.RowPsi.mk (_) (_) (_)
      (ψ := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).ψ : _)))
      (inj := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).inj : _)))
      (into := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).into : _)))
      (onto := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).onto : _))))
    (std := (by with_unfolding_all exact (ad.std :)))
    (eW := (by with_unfolding_all exact (ad.eW :)))
    (read := @fun x1 => @fun x2 => @fun x3 => @fun x4 => @fun x5 => kc% ((ad.read (kc% x1) (kc% x2) (kc% x3) (kc% x4) (kc% x5)).trans
      (congrFun_heq (g := (t.r.Y.IL.jMt (kc% x1) (kc% x2) (kc% x3) (kc% x4)).1) (f := kc% (IL'.jMt x1 x2 x3 x4).1)
        (kc% (hj (kc% x1) (kc% x2) (kc% x2) (kc% x3) (kc% x4))) _).symm))
    (rat := (by with_unfolding_all exact (ad.rat :)))
    (wt := (by with_unfolding_all exact (ad.wt :)))
    (id := (by with_unfolding_all exact (ad.id :)))
    )
    ((by with_unfolding_all exact (fi :)))
    (@Formalism.IndefR.NX.NExpHeckeRowX.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ((by with_unfolding_all exact (hrow.tie :))))
    ((by with_unfolding_all exact (cHk :)))
    ⟨(by with_unfolding_all exact (Sb :)), (by with_unfolding_all exact (ev :)), (by with_unfolding_all exact (hSb :)), (by with_unfolding_all exact ((s6.trans hev) :)), fun i σ k P α Rr hd => (by with_unfolding_all exact ((hE (kc% i) (kc% σ) k (kc% P) (kc% α) (kc% Rr)
      ⟨kc% (@HkDat.split (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.offS (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd),
        kc% (@HkDat.odd (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.le (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd),
        kc% (@HkDat.elt (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.reps (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd)⟩) :))⟩
    ((by with_unfolding_all exact (ser' :))
    )
    ((by with_unfolding_all exact (((mvOf w Z S' N h).tauTrue tau) :)))
    ⟨@_root_.GlobalTheory.GeoTie.ThetaTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (side := @fun x1 => @fun x2 => @fun x3 => @_root_.GlobalTheory.GeoTie.SideTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
      (pt := (by with_unfolding_all exact ((@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo ((x1)) ((x2)) ((x3))).pt : _)))
      (cover := (by with_unfolding_all exact ((@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo ((x1)) ((x2)) ((x3))).cover : _)))
      (ev_eq := (by with_unfolding_all exact ((@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo ((x1)) ((x2)) ((x3))).ev_eq : _)))
      (fmUr := (by with_unfolding_all exact ((@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo ((x1)) ((x2)) ((x3))).fmUr : _)))
      (hk := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).hk)
      (hk_none := (by with_unfolding_all exact ((@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo ((x1)) ((x2)) ((x3))).hk_none : _))))
    (isUnramified₂ := (by with_unfolding_all exact (geo.isUnramified₂ :)))
    ⟩
    ((by with_unfolding_all exact (ok :))) ((by with_unfolding_all exact (th :))) ((by with_unfolding_all exact (xda :))) ((by with_unfolding_all exact (((mvOf w Z S' N h).large large) :))) ((by with_unfolding_all exact (i1 :))) ((by with_unfolding_all exact (i2 :))) ((by with_unfolding_all exact (i3 :)))⟩⟩

end GlobalTheory.LayerMove
end
