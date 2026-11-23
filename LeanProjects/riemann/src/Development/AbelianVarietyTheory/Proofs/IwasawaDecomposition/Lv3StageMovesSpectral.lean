import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeptChoiceUpperLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLatticesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.HeightCounting.Up

theorem kept_trans_layer {D D' D'' : D7} {c : NChoice D} {c' : NChoice D'} {c'' : NChoice D''} (h : Kept c c') (h' : Kept c' c'') :
    Kept c c'' :=
  ⟨⟨h.gal.R.trans h'.gal.R, h.gal.host.trans h'.gal.host, h.gal.loc.trans h'.gal.loc, h.gal.Om.trans h'.gal.Om, h.gal.instOm.trans h'.gal.instOm, h.gal.algOm.trans h'.gal.algOm, h.gal.plOm.trans h'.gal.plOm, h.gal.PlG.trans h'.gal.PlG⟩,
    ⟨h.set.cc.trans h'.set.cc, h.set.Tw.trans h'.set.Tw, h.set.l.trans h'.set.l, h.set.O0.trans h'.set.O0, h.set.crO0.trans h'.set.crO0, h.set.algO0.trans h'.set.algO0, h.set.topO0.trans h'.set.topO0, h.set.O.trans h'.set.O, h.set.crO.trans h'.set.crO, h.set.algO.trans h'.set.algO, h.set.Ok.trans h'.set.Ok, h.set.crOk.trans h'.set.crOk, h.set.algOk.trans h'.set.algOk, h.set.zk.trans h'.set.zk, h.set.pD.trans h'.set.pD, h.set.chi1.trans h'.set.chi1, h.set.Sig.trans h'.set.Sig, h.set.finSig.trans h'.set.finSig, h.set.jS.trans h'.set.jS, h.set.side.trans h'.set.side, h.set.rhoS.trans h'.set.rhoS, h.set.S0.trans h'.set.S0, h.set.hEig.trans h'.set.hEig, h.set.abelian₂.trans h'.set.abelian₂, h.set.sideL.trans h'.set.sideL, h.set.RCG.trans h'.set.RCG, h.set.grpRCG.trans h'.set.grpRCG, h.set.finRCG.trans h'.set.finRCG, h.set.art.trans h'.set.art, h.set.th.trans h'.set.th⟩,
    ⟨h.forms.Fm.trans h'.forms.Fm, h.forms.acgFm.trans h'.forms.acgFm, h.forms.modFmK.trans h'.forms.modFmK, h.forms.modFmO.trans h'.forms.modFmO, h.forms.actG.trans h'.forms.actG, h.forms.U.trans h'.forms.U, h.forms.psiU.trans h'.forms.psiU, h.forms.eAlg.trans h'.forms.eAlg, h.forms.Dat.trans h'.forms.Dat, h.forms.th.trans h'.forms.th, h.forms.lev.trans h'.forms.lev, h.forms.thPsi.trans h'.forms.thPsi, h.forms.MtV.trans h'.forms.MtV, h.forms.acgMt.trans h'.forms.acgMt, h.forms.modMtK.trans h'.forms.modMtK, h.forms.modMtO.trans h'.forms.modMtO, h.forms.MtLat.trans h'.forms.MtLat, h.forms.thP.trans h'.forms.thP, h.forms.hkF.trans h'.forms.hkF⟩,
    h.br.trans h'.br, h.twI.trans h'.twI, h.sd.trans h'.sd, h.Q.trans h'.Q, h.k.trans h'.k, h.psi.trans h'.psi⟩

theorem org_of_kept {hL : GlobalTheory.Published.LocalLanglandsGL} {cDep : ℝ} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {D D' : D7} {Wt : Set B.places.Pl} {nch : NChoice D} {nch' : NChoice D'}
    (h : Org hL cDep K w Wt nch) (hk : Kept nch nch') : Org hL cDep K w Wt nch' := by
  obtain ⟨P, x, l, h1, h2, h3⟩ := h
  exact ⟨P, x, l, h1, h2, kept_trans_layer h3 hk⟩

set_option maxHeartbeats 4000000 in

theorem lv3Mv_true : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (S : SExt) (Γ : GeoP), LevelThreeCondition (prmR (NEo hL cDep) S Γ).s ∧ LevelThreeCondition (prmR (NEog hL cDep) S Γ).s := by
  intro hL cDep S Γ
  constructor
  · intro K B f T w Z l S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨nch', xd', hk, -, hn, -, hnx⟩ := GlobalTheory.T.exists_kept_choice_upper_lattice hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨n'⟩ := hn l.n
    obtain ⟨rx'⟩ := hrx ⟨l.rx⟩
    obtain ⟨c, ⟨e, ⟨pin⟩⟩, ⟨org⟩⟩ := l.nx
    obtain ⟨⟨c', e'⟩⟩ := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨e', ⟨pin'⟩⟩, ⟨org_of_kept org hk⟩⟩, hpk⟩
  · intro K B f T w Z l S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨nch', xd', hk, -, hn, hg, hnx⟩ := GlobalTheory.T.exists_kept_choice_upper_lattice hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨n'⟩ := hn l.n
    obtain ⟨rx'⟩ := hrx ⟨l.rx⟩
    obtain ⟨c, ⟨⟨e, ⟨pin⟩⟩, ⟨org⟩⟩, ⟨good⟩⟩ := l.nx
    obtain ⟨⟨c', e'⟩⟩ := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨⟨e', ⟨pin'⟩⟩, ⟨org_of_kept org hk⟩⟩, ⟨hg good⟩⟩, hpk⟩

end GlobalTheory.HeightCounting.Up
