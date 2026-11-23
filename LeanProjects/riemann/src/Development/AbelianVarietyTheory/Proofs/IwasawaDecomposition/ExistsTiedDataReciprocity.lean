import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtraTiedCol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NTiedAllAtWit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsTwTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DtTiedTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardCodeWordStagesFiniteGroupEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

open Formalism.L2 in
set_option maxHeartbeats 1000000 in

theorem tiedDataS_assemble {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} (ex : Extra D L hT Gi Gl K Y cX)
    (host : Formalism.L2.Host.HostTied D) (level : Formalism.L2.Host.LevelTied D) (cols : Formalism.L2.Forms.ColsTiedSym D) (full : Formalism.L2.Forms.ColsFullS cols)
    (extra : Formalism.L2.Forms.ColsExtraTiedS full ex) (provA : Formalism.BasicNotions.TH.ProvA) (theta : Formalism.L2.Theta.AllTied D ex.th provA) (twIn : Formalism.MainNotions.TwIn D)
    (n : Formalism.L2.NormalizedTwistCompatibility D ex.nch twIn) (frameN : ∀ x, n.gal.fr.jE x = host.fr.j x)
    (cf : Formalism.L2.Host.CharFrame D) (tp : Formalism.L2.Host.TupTied D cf ex.nch)
    (h : (⟨n.cf, n.tp⟩ : Σ c : Formalism.L2.Host.CharFrame D, Formalism.L2.Host.TupTied D c ex.nch) = ⟨cf, tp⟩)
    (thetaChr : Formalism.L2.Host.ThetaChrTied D cf ex.nch tp ex.th) (chrVal : Formalism.L2.Host.ValLL0 D cf) (chrDt : Formalism.L2.Host.DtTied D cf)
    (chrN : Formalism.L2.Host.NCharTied D cf ex.nch tp) (chrGal : Formalism.L2.Host.NGalChrTied D cf ex.nch tp)
    (chrPsi : Formalism.L2.Host.PsiChoiceCompatible D cf ex.nch tp) (sameChr : Formalism.L2.JoinChr.SameChr theta.T thetaChr)
    (what₂ : Formalism.L2.Rows.RowsCompatible D host cf tp) (inK : Y.Lev → ℕ → Prop) (geo : Formalism.L2.Geo.GeoTiedP Y inK)
    (tw0 : TwForms D) (he : ex.tw = tw0) (tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes tp cols tw0) (emt : Formalism.L2.Rows.EMtTied D cols tw)
    (g : Formalism.L2.G.GroupCompatibilityAll D hT ex.cmp) (herm_eq : g.herm = full.1.to0) (forms_eq : g.forms = fun u => (cols.forms u).to0)
    (P : ∀ (c : Formalism.L2.Host.CharFrame D) (t : Formalism.L2.Host.TupTied D c ex.nch) (C : Formalism.L2.Forms.ColsTiedSym D), Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes t C tw0 → Prop)
    (hP : P cf tp cols tw) :
    ∃ S : Formalism.L2.LinkedFamilyData ex, S.host = host ∧ S.cols = cols ∧ HEq S.full full ∧ S.g = g ∧
      (⟨S.provA, S.theta⟩ : Σ a, Formalism.L2.Theta.AllTied D ex.th a) = ⟨provA, theta⟩ ∧
      (⟨S.twIn, S.n⟩ : Σ I, Formalism.L2.NormalizedTwistCompatibility D ex.nch I) = ⟨twIn, n⟩ ∧ HEq S.thetaChr thetaChr ∧
      (∀ a, S.chrDt.eDt a = chrDt.eDt a) ∧
      (S.what₂.O.pieces.rcf = what₂.O.pieces.rcf ∧ S.what₂.O.pieces.MDel = what₂.O.pieces.MDel) ∧
      S.inK = inK ∧ HEq S.geo geo ∧ P _ _ _ (he ▸ S.tw) := by
  cases h
  subst he
  first
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, frameN := frameN, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩

theorem ColW.cf_eq {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) :
    Fr.at (w.st Z) f = TC.cf w.I w.l Z := by
  have h := w.C_eq
  have : Fr.at (w.st Z) w.I.C = TC.cf w.I w.l Z := rfl
  rw [← this, h]

set_option maxHeartbeats 2000000 in

theorem WPt.tiedDataS_pinned : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) → Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → ∃ S : Formalism.L2.LinkedFamilyData q.O.ex, SPin q S := by
  intro hA hW hL p K q hlev hze
  obtain ⟨extra, g, hg, hherm, hforms⟩ := WPt.extraTied_col p.s K q
  obtain ⟨I, n, hE, hgood, hchr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := nTiedAll_atWit hL p K q
  obtain ⟨he, tw, hstd, emt⟩ := GlobalTheory.Mem.Top.Bl.WPt.colsTwTied p.s K q
  obtain ⟨dt, hdt⟩ := TC.dtTied_true q.w.I q.w.ok q.w.pins q.w.l q.Z
  have hO : ∃ O : Formalism.L2.Rows.OTied (q.w.D q.Z) q.core.a.host (TC.cf q.w.I q.w.l q.Z),
      O.pieces.rcf = GlobalTheory.Mem.HD.qb q.core.a.host.fr.ι q.w.δ.ray ∧ O.pieces.MDel = GlobalTheory.Mem.HD.qb q.core.a.host.fr.ι q.w.δ.M' := by
    generalize q.core.a.host = H
    rw [← ColW.cf_eq]
    exact GlobalTheory.Mem.CyclotomicFieldContainment.oTied_of_ksExact hA hW (q.w.st q.Z) q.f q.w.δ q.w.exact H
  obtain ⟨O, hO1, hO2⟩ := hO
  have hval : Formalism.L2.Host.ValLL0 (q.w.D q.Z) (TC.cf q.w.I q.w.l q.Z) := by
    rw [← ColW.cf_eq]
    exact q.w.val _ _ _ _ _ _
  have hfr : ∀ x, n.gal.fr.jE x = q.core.a.host.fr.j x := by
    rw [h1]
    exact q.core.a.frameN
  obtain ⟨S, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    tiedDataS_assemble q.O.ex q.core.a.host hlev q.x.col.C q.x.col.full extra q.x.th.provA q.x.th.all I n hfr
      (TC.cf q.w.I q.w.l q.Z) q.x.n.tp hchr q.x.th.chr hval dt q.core.a.chrN q.core.a.chrGal q.x.n.chrPsi q.x.th.same
      ⟨O, q.O.ex.kap_def, hze⟩ q.x.div.inK q.x.div.geo (q.w.tw q.Z) he tw emt g hherm hforms
      (fun _ _ _ t => TC.StdTw q.w.I q.w.l q.Z q.w.l0 t) hstd
  have key : ∀ Q : (Σ I, Formalism.L2.NormalizedTwistCompatibility (q.w.D q.Z) q.O.ex.nch I) → Prop, Q ⟨I, n⟩ → Q ⟨S.twIn, S.n⟩ :=
    fun Q hQ => s6 ▸ hQ
  refine ⟨S, s1, s2, s3, s4 ▸ hg, s5, key (fun z => z.1.E = _) hE, key (fun z => DQ.GoodAllAt _ _ z.1) hgood,
    key (fun z => (⟨z.2.cf, z.2.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = _) hchr,
    key (fun z => z.2.gal = _) h1, key (fun z => z.2.n = _) h2, key (fun z => z.2.exp = _) h3,
    key (fun z => z.2.chiD = _) h4, key (fun z => z.2.twF = _) h5, key (fun z => HEq z.2.types _) h6,
    key (fun z => HEq z.2.cover _) h7, key (fun z => z.2.plB = _) h8, s7, fun a => (s8 a).trans (hdt a), ?_, s10, s11, he, s12⟩
  rw [s9.1, s9.2, s1]
  exact ⟨hO1, hO2⟩

end GlobalTheory.Mem.Top.Bl
