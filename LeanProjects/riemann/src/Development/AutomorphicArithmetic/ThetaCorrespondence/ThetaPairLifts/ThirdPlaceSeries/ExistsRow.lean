import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongrFunHeq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtSame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Inner
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TauTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTiedRowLoc
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D)
theorem Mv.rowLoc_alt {D : D7} (m : Mv D) {C : NChoice D} (a : _root_.GlobalTheory.HeightCounting.NAllCAlt D C) (F : Formalism.L2.RowFrame D) (F' : Formalism.L2.RowFrame m.D)
    (hF : HEq F'.rep F.rep) (x : _root_.Formalism.L2.RowLocTiedAlt D a.gal.lp F) : _root_.Formalism.L2.RowLocTiedAlt m.D ((_root_.UpperTheory.One.M.mvAll_alt trivial) m a).gal.lp F' := by
  obtain ⟨rep, inj⟩ := F
  obtain ⟨rep', inj'⟩ := F'
  have e : rep' = kc% rep := eq_of_heq (kc% hF)
  subst e
  exact (@_root_.Formalism.L2.RowLocTiedAlt.mk (_) (_) (_)
    (sat := kc% x.sat)
    )
theorem exists_nonempty_nMore_upL (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z))
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0')
    (hs : RowsSame t t') (hg : HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo))
    (hj : ∀ (μ : (w.D Z).what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ) (hμ' : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ) (i : Fin (w.D Z).R.m) (x : (w.D Z).what₂.Mt μ ((i : ℕ) + 1)), HEq (t'.r.Y.IL.jMt μ hμ' i x).1 (t.r.Y.IL.jMt μ hμ i x).1)
    (hser : ∀ (kKs : ↥t.r.z.core.Q.c.F →+* ↥(w.st Z).toD7.LL0) (hk : ∀ x, ((kKs x : ↥(w.st Z).toD7.LL0) : (w.st Z).toD7.what₂.LL) = algebraMap _ (w.st Z).toD7.what₂.LL x) (YS : Formalism.IndefR.NX.NExpRealS t.r.z.R t.r.z.cG (Formalism.IndefR.NX.ratDatR t.r.z.R t.r.z.cG kKs hk)) (kKs' : ↥t'.r.z.core.Q.c.F →+* ↥(w.st (upL Z S' N h)).toD7.LL0) (hk' : ∀ x, ((kKs' x : ↥(w.st (upL Z S' N h)).toD7.LL0) : (w.st (upL Z S' N h)).toD7.what₂.LL) = algebraMap _ (w.st (upL Z S' N h)).toD7.what₂.LL x) (YS' : Formalism.IndefR.NX.NExpRealS t'.r.z.R t'.r.z.cG (Formalism.IndefR.NX.ratDatR t'.r.z.R t'.r.z.cG kKs' hk')), HEq kKs' kKs → HEq YS'.fi YS.fi → HEq YS'.eF YS.eF → ∀ (a : _root_.GlobalTheory.HeightCounting.NAllCAlt (w.D Z) nch) (X' : Formalism.L2.NExpTied (w.st (upL Z S' N h)).toD7), HEq X' ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a).exp → ∀ (PV : ∀ i : Fin (w.st Z).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV) (PV' : ∀ i : Fin (w.st (upL Z S' N h)).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (upL Z S' N h)).toD7 i) (w.st (upL Z S' N h)).toD7.R.nV), HEq (fun i => (PV' i).ψ) (fun i => (PV i).ψ) → ∀ Pq Pq', HEq Pq' Pq → SerAt (D := (w.st Z).toD7) YS t.r.z.geo.v₀ a.exp PV (TC.cf w.I w.l Z) Pq → Nonempty (SerAt (D := (w.st (upL Z S' N h)).toD7) YS' t'.r.z.geo.v₀ X' PV' (TC.cf w.I w.l (upL Z S' N h)) Pq'))
    {tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch} {tp' : TupTied (w.D (upL Z S' N h)) (TC.cf w.I w.l (upL Z S' N h)) (nchUp S' N h nch)}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (w.D Z) (TC.cf w.I w.l Z) nch tp)
    (a' : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (w.D (upL Z S' N h)) (TC.cf w.I w.l (upL Z S' N h)) (nchUp S' N h nch) tp') (hA : _root_.GlobalTheory.LayerMove.AtSameAltAlt (mvOf w Z S' N h) a a')
    (r : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := (w.st Z).toD7) a t.r.z.R t.r.z.F t.r.z.cG t.r.Y) (e : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) r t.r.z.geo xd) :
    ∃ r' : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := (w.st (upL Z S' N h)).toD7) a' t'.r.z.R t'.r.z.F t'.r.z.cG t'.r.Y,
      Nonempty (_root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st (upL Z S' N h)).toD7) r' t'.r.z.geo (xdUp S' N h xd)) := by
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
  have e7 : geo' = kc% (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) := eq_of_heq (kc% hg)
  subst e7
  obtain ⟨nt', all', chr_eq', host', frameN', chrN', chrGal', Pq', Pq_over', pq', jE_eq', mt_eq', Pq_eq', hlow', split', ratIn',
    r1', r2', r3', depth'⟩ := a'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hA
  have e8 : all' = kc% ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a.all) := eq_of_heq (kc% s1)
  have e9 : Pq' = kc% a.Pq := eq_of_heq (kc% s2)
  subst e8 e9
  obtain ⟨kKs, hk, nexp, hecke, grp, rowLoc, S_eq, hL_eq, rep_eq⟩ := r
  obtain ⟨ad, fi, hrow, cHk, eig, ser, tau, geo, ok, th, xda, large, labc, zeta, pht⟩ := e
  obtain ⟨geo⟩ := geo
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, IL', _, _, _, eFT', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨eW', _⟩, _⟩ := Y'
  have e10 : eW' = kc% t.r.Y.mj.eW := eq_of_heq (kc% hs.eW)
  subst e10
  obtain ⟨Sb, ev, hSb, hev, hE⟩ := eig
  obtain ⟨i1, i2, i3⟩ := s7 ⟨labc, zeta, pht⟩
  obtain ⟨l1, l2, l3, l4, l5, lv⟩ := grp.lvl
  refine Nonempty.elim (hser kKs hk nexp (kc% kKs) (kc% hk) (@_root_.Formalism.IndefR.NX.NExpRealS.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (fi := kc% nexp.fi)
    (geq := kc% nexp.geq)
    (rho := kc% nexp.rho)
    (chi := kc% nexp.chi)
    (eF := kc% nexp.eF)
    (bsup := kc% nexp.bsup)
    (act := kc% nexp.act)
    )
    (kc% (HEq.refl kKs)) (kc% (HEq.refl nexp.fi)) (kc% (HEq.refl nexp.eF)) a.all (kc% ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a.all).exp)
    (kc% (HEq.refl ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a.all).exp)) ad.PV (@fun x1 => @_root_.Formalism.IndefR.principalLevelFrame.RowPsi.mk (_) (_) (_)
      (ψ := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).ψ)
      (inj := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).inj)
      (into := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).into)
      (onto := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).onto))
    (kc% (HEq.refl fun i => (ad.PV i).ψ)) a.Pq (kc% a.Pq) (kc% (HEq.refl a.Pq)) ser) fun ser' => ?_
  refine ⟨@_root_.GlobalTheory.Mem.Top.Bl.NormRealisationData.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (kc% kKs) (kc% hk)
    (@_root_.Formalism.IndefR.NX.NExpRealS.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (fi := kc% nexp.fi)
    (geq := kc% nexp.geq)
    (rho := kc% nexp.rho)
    (chi := kc% nexp.chi)
    (eF := kc% nexp.eF)
    (bsup := kc% nexp.bsup)
    (act := kc% nexp.act)
    )
    (@_root_.Formalism.IndefR.NX.NExpRealH.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (hL := kc% hecke.hL)
    (hs := kc% hecke.hs)
    (cHk := kc% hecke.cHk)
    (cHk_zero := kc% hecke.cHk_zero)
    (cHk_unit := kc% hecke.cHk_unit)
    (cHk_pow := kc% hecke.cHk_pow)
    (hkEq := kc% hecke.hkEq)
    )
    (@_root_.Formalism.L2.DIV.GrpTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (card := kc% grp.card)
    (e0 := kc% grp.e0)
    (lvl0 := kc% grp.lvl0)
    (psi0 := kc% grp.psi0)
    (idxSharp := kc% grp.idxSharp)
    (lvl := ⟨kc% l1, kc% l2, kc% l3, kc% l4, kc% l5,
      ⟨kc% lv.place, kc% lv.comp, kc% lv.gen, kc% lv.p0, kc% lv.chi0, kc% lv.ps, kc% lv.chis⟩⟩)
    )
    (kc% ((mvOf w Z S' N h).rowLoc_alt a.all _ (kc% (Formalism.L2.Col.rowFrameOf (w.D (upL Z S' N h)) _ eFT')) (kc% hs.rep) rowLoc))
    (kc% (s3.trans S_eq)) (kc% (s4.trans hL_eq)) (kc% ((s5.trans rep_eq).trans hs.rep.symm)), ⟨@_root_.GlobalTheory.HeightCounting.RealExpansionExtraData.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (@_root_.GlobalTheory.HeightCounting.MtAd.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (PV := @fun x1 => @_root_.Formalism.IndefR.principalLevelFrame.RowPsi.mk (_) (_) (_)
      (ψ := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).ψ)
      (inj := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).inj)
      (into := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).into)
      (onto := kc% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (kc% x1)).onto))
    (std := kc% ad.std)
    (eW := kc% ad.eW)
    (read := @fun x1 => @fun x2 => @fun x3 => @fun x4 => @fun x5 => kc% ((ad.read (kc% x1) (kc% x2) (kc% x3) (kc% x4) (kc% x5)).trans
      (congrFun_heq (g := (t.r.Y.IL.jMt (kc% x1) (kc% x2) (kc% x3) (kc% x4)).1) (f := kc% (IL'.jMt x1 x2 x3 x4).1)
        (kc% (hj (kc% x1) (kc% x2) (kc% x2) (kc% x3) (kc% x4))) _).symm))
    (rat := kc% ad.rat)
    (wt := kc% ad.wt)
    (id := kc% ad.id)
    )
    (kc% fi)
    (@Formalism.IndefR.NX.NExpHeckeRowX.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (kc% hrow.tie))
    (kc% cHk)
    ⟨kc% Sb, kc% ev, kc% hSb, kc% (s6.trans hev), fun i σ k P α Rr hd => kc% (hE (kc% i) (kc% σ) k (kc% P) (kc% α) (kc% Rr)
      ⟨kc% (@HkDat.split (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.offS (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd),
        kc% (@HkDat.odd (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.le (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd),
        kc% (@HkDat.elt (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.reps (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd)⟩)⟩
    (kc% ser'
    )
    (kc% ((mvOf w Z S' N h).tauTrue_alt tau))
    ⟨@_root_.GlobalTheory.GeoTie.ThetaTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (side := @fun x1 => @fun x2 => @fun x3 => @_root_.GlobalTheory.GeoTie.SideTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
      (pt := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).pt)
      (cover := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).cover)
      (ev_eq := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).ev_eq)
      (fmUr := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).fmUr)
      (hk := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).hk)
      (hk_none := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).hk_none))
    (isUnramified₂ := kc% geo.isUnramified₂)
    ⟩
    (kc% ok) (kc% th) (kc% xda) (kc% ((mvOf w Z S' N h).large large)) (kc% i1) (kc% i2) (kc% i3)⟩⟩
end GlobalTheory.LayerMove
end
end
