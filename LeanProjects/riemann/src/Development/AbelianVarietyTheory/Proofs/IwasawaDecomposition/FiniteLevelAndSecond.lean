import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondGOfHalves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIsW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GensJAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstructionStartingChoicesOfFineAdelicDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtTwistedPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTransStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPosIffMemExample
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RawPackEqPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistOfSeedCharacterPowersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsAtOfPlUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BareStatementOfDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StatementAOfPhotonCompatStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StatementCOfCasselmanWallachStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MotiveBoundOfSeriesStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick avoidPlaces subset_avoidPlaces)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.Up

theorem pass_of {Q : V4.Slot} {p q r : AtP} (hp : Step KPx (fun _ _ _ _ => True) p) (hq : Step KPx (fun _ _ _ _ => True) q)
    (h : EvG fun K => ∀ B f T, K.Over B.toPre → KPx B f → T = TwDat.untw B T.pl → p K B f T →
      ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
        (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
        ExportAt (assemble B C W V S N G) c.O.nch c.O.xd →
        ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ), (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) →
          ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
            (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ KPx B' f' ∧ (q K B' f' T' → r K B' f' T')) :
    Pass KPx Q r := by
  classical
  refine (EvG.inter (EvG.inter hp hq) h).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hp, hq⟩, hr⟩ := H
  have hs' : large₂ K fun B f T => KPx B f → q K B f T :=
    (hq.inter (lg_forced K)).imp fun _ _ _ _ G a => G.1 a G.2 trivial
  obtain ⟨S₁, P₁, A₀, S₂₀, a₁, a₂, hlg⟩ := hs'
  have hb : large₂ K fun B f T => (∀ z ∈ S₁ B.toPre f B.KsC, z ∈ B.fixedCoefficientFieldInComplex) ∧ P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex ⊆ T.pl :=
    ⟨S₁, P₁, fun _ _ _ _ _ => ∅, S₂₀, a₁, a₂, fun _ _ _ _ h p _ => ⟨h.1, p⟩⟩
  refine (hp.inter hb).imp ?_
  rintro B f T hO ⟨hp, h₁, hpl₁⟩ hKP hT C W V S N G c q hx A S₂ hS₂
  obtain ⟨B', f', T', e, hf, hpl, hAv, hS', hK', hfin⟩ := hr B f T hO hKP hT (hp hKP c.forced trivial) C W V S N G c q hx
    (fun l => A l ∪ A₀ B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂₀ P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
    (fun P g Ξ z hz => (Finset.mem_union.1 hz).elim (hS₂ P g Ξ z) (a₂ P g _ _ Ξ z))
  have hP : B'.toPre = B.toPre := e.1
  have hk : B'.KsC = B.KsC := e.KsC_eq
  have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := e.fixedCoefficientField_eq
  have hO' : K.Over B'.toPre := hP ▸ hO
  have hLL : ∀ z ∈ S₂₀ B'.toPre f' B'.KsC B'.fixedCoefficientFieldInComplex (T'.set f'), z ∈ B'.LLC := by
    intro z hz
    rw [hk, hl] at hz
    obtain ⟨x, rfl⟩ := hS' z (Finset.mem_union_right _ hz)
    exact ⟨x, rfl⟩
  have hq' := hlg B' f' T' hO'
    ⟨by rw [hk, hl, secondG_congr S₁ hP hf]; exact h₁, hLL⟩
    (by rw [hk, hl, secondG_congr P₁ hP hf, hpl]; exact hpl₁)
    (fun w v hv hA => hAv w v hv (Finset.mem_union_right _ (by
      rw [hk, hl, secondG_congr A₀ hP hf] at hA; exact hA))) hK'
  exact ⟨B', f', T', e, hf, hpl, fun w v hv hA => hAv w v hv (Finset.mem_union_left _ hA),
    fun z hz => hS' z (Finset.mem_union_left _ hz), hfin hq'⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

theorem muIsW_st {P : Pre2 K w} (x : St P) : V4.MuIsW (w.st x.o.Z) f T P.Wt w.I.xi :=
  { inj := w.ok.xi_inj
    range := w.xi_range
    mu0 := w.l.xi0
    star := by
      show w.I.xi w.I.muStar = f.del
      rw [w.ok.xi_star, w.C_eq]
    star' := by
      show w.I.xi w.I.muStar' = f.del'
      rw [w.ok.xi_star', w.C_eq]
    tw := P.q.mu.tw
    on := P.q.mu.on
    off := P.q.mu.off
    sub := P.sub
    supp := P.supp }

theorem twisted_st {P : Pre2 K w} (x : St P) (v : B.places.Pl) : TwistedAt (Dof x) v ↔ v ∈ P.Wt :=
  (TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW_st x)).1 v

theorem below_plUnder {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} (h : Enl B B') (Z : w.Lt) (Z' : w'.Lt)
    (v' : B'.places.Pl) : Below (w.D Z) (w'.D Z') (plUnder h v') v' := by
  intro x x' e
  have : x' = RingOfIntegers.mapRingHom (TwChar.incl h) x :=
    RingOfIntegers.ext (B'.embLL.injective (e.symm.trans (TwChar.embLL_incl h _).symm))
  subst this
  exact TwChar.mem_plUnder h v' x

theorem sFino_of {hL : GlobalTheory.Published.LocalLanglandsGL} {cDep : ℝ} (h : SFinl hL cDep) : SFino hL cDep := by
  refine StepW.trans h (StepW.of_all fun K B f T w _ _ H P x l S Γ hl => ?_)
  obtain ⟨Z, v, h1, h2⟩ := H P x l S Γ hl.1
  exact ⟨Z, { g := v.g, coh := v.coh, Wt := v.Wt, p0 := v.p0, what₂ := v.what₂, rx := v.rx, nch := v.nch, n := v.n, xd := v.xd,
              chiT := v.chiT, nx := ⟨v.nx.1, v.nx.2, ⟨P, x, l, hl, h1, h2⟩⟩ }, h1, h2⟩

theorem overOne_plUnder_of {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} (h : Enl B B') (Z : w.Lt) (Z' : w'.Lt)
    {v₁ v₂ : B'.places.Pl} (ho : OverOne (w'.D Z') v₁ v₂) : OverOne (w.D Z) (plUnder h v₁) (plUnder h v₂) := by
  have hm : ∀ x : B.LL0, TwChar.incl h (x : B.LL) ∈ B'.LL0 := fun x => by
    obtain ⟨y, hy, e⟩ : B.embLL (x : B.LL) ∈ B'.embLL '' (B'.LL0 : Set B'.LL) := h.2.2.1 ▸ ⟨x, x.2, rfl⟩
    rwa [← B'.embLL.injective (e.trans (TwChar.embLL_incl h _).symm)]
  let j : B.LL0 →+* B'.LL0 := ((TwChar.incl h).comp B.LL0.val.toRingHom).codRestrict B'.LL0 hm
  intro x
  let x' : 𝓞 ↥(w'.D Z').LL0 := RingOfIntegers.mapRingHom j x
  have key : ∀ v : B'.places.Pl, 0 < (w.D Z).what₂.places.val (plUnder h v) ((x : ↥(w.D Z).LL0) : (w.D Z).what₂.LL) ↔
      0 < (w'.D Z').what₂.places.val v ((x' : ↥(w'.D Z').LL0) : (w'.D Z').what₂.LL) :=
    fun v => (val_pos_iff_mem (w.D Z) _ x).trans (((TwChar.mem_plUnder h v _).trans (iff_of_eq (congrArg
      (· ∈ HeightOneSpectrum.asIdeal v) (RingOfIntegers.ext rfl)))).trans (val_pos_iff_mem (w'.D Z') v x').symm)
  exact (key v₁).trans ((ho x').trans (key v₂).symm)

theorem exists_of_position {P : CP} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {c : V4.Core K X f T} (h : positionOf P K X f T c) :
    ExportAt X.toD7 c.O.nch c.O.xd → ∃ (w : ColW X.B f T) (Z : w.Lt) (c' : V4.Core K (w.st Z) f T), P K X.B f T w Z c' ∧
      ExportAt (w.st Z).toD7 c'.O.nch c'.O.xd :=
  positionOf_ind (R := fun K X f T c => ExportAt X.toD7 c.O.nch c.O.xd → ∃ (w : ColW X.B f T) (Z : w.Lt)
    (c' : V4.Core K (w.st Z) f T), P K X.B f T w Z c' ∧ ExportAt (w.st Z).toD7 c'.O.nch c'.O.xd)
    (fun _ _ _ _ w Z c h e => ⟨w, Z, c, h, e⟩) h

theorem SameGal.trans {D D' D'' : D7} (h : SameGal D D') (h' : SameGal D' D'') : SameGal D D'' :=
  ⟨⟨h.gal.R.trans h'.gal.R, h.gal.host.trans h'.gal.host, h.gal.loc.trans h'.gal.loc, h.gal.Om.trans h'.gal.Om,
    h.gal.instOm.trans h'.gal.instOm, h.gal.algOm.trans h'.gal.algOm, h.gal.plOm.trans h'.gal.plOm, h.gal.PlG.trans h'.gal.PlG⟩,
    h.pl.trans h'.pl⟩

theorem enl_refl (B : Base) : Enl B B := ⟨rfl, rfl, rfl, subset_rfl⟩

theorem avPrimes_st (Z Z' : w.Lt) : avPrimes (w.st Z).toD7 = avPrimes (w.st Z').toD7 := rfl

theorem exists_seed {hL : GlobalTheory.Published.LocalLanglandsGL} {cDep : ℝ} {S : SExt} {Γ : GeoP} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (prmR (NEo hL cDep) S Γ).s K w Z c) (e : ExportAt (w.st Z).toD7 c.O.nch c.O.xd) :
    ∃ (P : Pre2 K w) (x : St P) (_ : LC hL x), (ListSt cDep x ∧ SatU P) ∧ ∀ A, Nonempty (Seed (Dof x) A) := by
  obtain ⟨P, x, l, hl, hW, hk⟩ := b.nx.2.2.down
  have key := (TupTieW.tupTied_of_muIsW (w.st Z) f T c.Wt c.xi c.mu).1
  refine ⟨P, x, l, hl, GlobalTheory.HeightCounting.Up.nonempty_seed_of_kept (Dof x) (w.st Z).toD7 l.c.ch c.O.nch c.O.xd hk rfl (fun v v₀ hv ht => ?_) l.c.side.nct
    l.c.side.choice.twI_conj ?_ B.coeffGaloisSubfield_isGalois (twistedPlaceIndex_mem_firstPair_of_compatibleChoice (w.st Z).toD7 c.O.nch c.nch_tie B.coeffGaloisSubfield_isGalois) e b.nx.2.1.1.1.xd⟩
  · obtain rfl : v = v₀ := eq_of_heq hv
    exact (key v).2 (hW ▸ (twisted_st x v).1 ht)
  · exact (TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW_st x)).2.1.subset fun v hv => (twisted_st x v).1 hv

theorem goodO_of (hP : PrN) {hL : GlobalTheory.Published.LocalLanglandsGL} {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}
    (h : Enl B B') {P : Pre2 K w} (x : St P) {A} (σ : Seed (Dof x) A) (hA : ∀ i, avD (Dof x) (avDesign (Dof x)) i ⊆ A i)
    (hT : TwFrom (w.st x.o.Z) σ h T') {P' : Pre2 K w'} (hW : ∀ v', plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt) {y : St P'} (l : LC hL y)
    (hc : Carried (Dof x) (Dof y)) (hs : ∀ v', HEq (l.c.ch.twI v') (σ.s (plUnder h v'))) {Z : w'.Lt}
    {C : NChoice (w'.st Z).toD7} {xd : ThData (w'.st Z).toD7} (hk : Kept l.c.ch C) (hx : XdAll xd)
    (hZ : ∀ v', TwistedAt (w'.st Z).toD7 v' → v' ∈ P'.Wt) : GoodO (w'.st Z).toD7 C xd := by
  classical
  refine GlobalTheory.T.goodTwist_of_seed_character_powers (Dof x) (Dof y) (w'.st Z).toD7 A σ l.c.ch C xd (plUnder h) hc.exp hk (avPrimes_st _ _) rfl hx hA
    fun v₂ v₃ hv ht => ?_
  obtain rfl : v₂ = v₃ := eq_of_heq hv
  have h1 := hZ v₂ ht
  have h2 : TwistedAt (Dof x) (plUnder h v₂) := (twisted_st x _).2 ((hW _).2 h1)
  have h3 : TwistedAt (Dof y) v₂ := (twisted_st y _).2 h1
  obtain ⟨hQ, hk', ι, χ, hF, hχ⟩ := (hT.2 v₂).1 h2
  have hg := (((σ.good _ h2).2 1 (by simp)).1)
  rw [zpow_one] at hg
  have e1 : l.c.ch.Q v₂ = T'.Q v₂ := (congrFun l.c.Q_eq v₂).trans (if_pos h1)
  have e2 : l.c.ch.k' v₂ = T'.k v₂ := l.c.k_eq v₂ h3
  refine ⟨h2, GlobalTheory.HeightCounting.Rigid.rawPack_eq_pow hP (Dof x) (Dof y) (σ.pack (plUnder h v₂)) _ ι χ (cfOf y) l.c.ch l.c.tp v₂ hc.exp hg hF l.c.side.psi h3
    (hs v₂) ((heq_of_eq e1).trans hQ) (e2.trans hk') ((heq_of_eq (congrFun l.c.psi_eq v₂)).trans hχ) fun z hz => ?_⟩
  rw [e2] at hz
  exact hT.1 v₂ z hz

theorem has3_of {hL : GlobalTheory.Published.LocalLanglandsGL} {cDep : ℝ} (hP : PrN) (S : SExt) (Γ : GeoP) {B' : Base} {f' : Fr B'.toPre}
    {T' : TwDat B'} {w' : ColW B' f' T'} (h : Enl B B') {P : Pre2 K w} (x : St P) {A} (σ : Seed (Dof x) A)
    (hA : ∀ i, avD (Dof x) (avDesign (Dof x)) i ⊆ A i) (hT : TwFrom (w.st x.o.Z) σ h T') {P' : Pre2 K w'}
    (hW : ∀ v', plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt) {y : St P'} (l : StrictHenselianAcyclic hL y) (hc : Carried (Dof x) (Dof y)) (hl : ListSt cDep y ∧ SatU P')
    (ck : ∀ s : B'.places.Pl → (Dof y).ntw.Tw, (∀ v, ∃ b, ReadsAt (D := Dof y) (s v) b v) → (∀ v, s (B'.places.conj v) = s v) →
      ∃ c : StC l.mt l.b T'.k T'.psi, c.ch.twI = s)
    (fin : ∀ (l : LC hL y) (S : SExt) (Γ : GeoP), (ListSt cDep y ∧ SatU P') →
      ∃ (Z : w'.Lt) (v : Lv3 (prmR (NEo hL cDep) S Γ).s K w' Z), v.Wt = P'.Wt ∧ Kept l.c.ch v.nch) :
    Has3 (prmR (NEog hL cDep) S Γ).s K B' f' T' w' := by
  have eT : (Dof x).ntw.Tw = (Dof y).ntw.Tw := (same_basic hc.exp.gal hc.exp.set hc.exp.frm).1
  obtain ⟨c, hs⟩ := ck (fun v' => cast eT (σ.s (plUnder h v')))
    (fun v' => (σ.reads (plUnder h v')).imp fun b hb =>
      GlobalTheory.HeightCounting.Up.readsAt_of_plUnder (w.st x.o.Z) (w'.st y.o.Z) h hc v' _ _ b (cast_heq eT _).symm hb)
    (fun v' => congrArg (cast eT) ((congrArg σ.s (TwChar.plUnder_conj h v')).trans (σ.conj _)))
  obtain ⟨Z, v, h1, h2⟩ := fin { toStrictHenselianAcyclic := l, c := c } S Γ hl
  have hg : GoodO (w'.st Z).toD7 v.nch v.xd :=
    goodO_of hP h x σ hA hT hW { toStrictHenselianAcyclic := l, c := c } hc (fun v' => (heq_of_eq (congrFun hs v')).trans (cast_heq eT _)) h2
      v.nx.2.1.1.1.xd fun v' hv' => h1 ▸ ((TupTieW.tupTied_of_muIsW (w'.st Z) f' T' v.Wt w'.I.xi v.what₂.mu).1 v').1 hv'
  exact ⟨Z, ⟨{ g := v.g, coh := v.coh, Wt := v.Wt, p0 := v.p0, what₂ := v.what₂, rx := v.rx, nch := v.nch, n := v.n, xd := v.xd,
               chiT := v.chiT, nx := ⟨v.nx.1, v.nx.2, ⟨hg⟩⟩ }⟩⟩

theorem secondNo_of (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : PrN) (hS : SerN) (hD : DatExt) (hH : WeightCaseCondition) (hds : GlobalTheory.Published.DiscreteSeriesExists)
    (hc : PhtCmp) {hL : GlobalTheory.Published.LocalLanglandsGL} (hMt : SMt) (hRat : SRat hL) (hCu : SCusp hL) {cDep : ℝ}
    (hF : SFinl hL cDep) : SecondNo hL cDep := by
  classical
  intro S Γ
  have h3 := GlobalTheory.Mem.R3.Rw.Second.exists_ext_twisted_places hP.greenC hD
  have h4 := (GlobalTheory.T.constructionStartingChoices_of_fine_adelicData GlobalTheory.weilRepresentationUnitaryPair hds hP.hc hP.decay hH).and ((GlobalTheory.T.bare_statement_of_discrete_series hP hds).and ((GlobalTheory.T.statement_a_of_point_compat hP hc hL).and
    (hMt.and (hRat.and (hCu.and ((GlobalTheory.T.motive_bound_of_series hP hS hL).and ((GlobalTheory.T.statement_c_of_casselman_wallach hCo hCW hHM hP hS hL).and (sFino_of hF))))))))
  refine pass_of (p := fun _ _ _ _ => True) (Step.of_all fun _ _ _ _ _ _ _ h => h) (Step.and h3 h4)
    (EvG.imp GlobalTheory.Mem.Top.ReW.extend_pinned fun K _ _ _ _ hw2 => ?_)
  intro B f T hO hKP hT _ C W V S' N G c₀ hQ hE A S₂ hS₂
  obtain ⟨w, Z, c, ⟨b, -⟩, e⟩ := exists_of_position hQ hE
  have hSt : Start K B f T w := ⟨⟨b.pin⟩, Or.inl hT, b.coh⟩
  obtain ⟨P, x, l, hl, hσ⟩ := exists_seed b e
  obtain ⟨A₁, S₁, a₁, hw'⟩ := hw2 B f T w hO ⟨b.pin⟩
  obtain ⟨σ⟩ := hσ fun i => avD (Dof x) (avDesign (Dof x)) i ∪ avoidPlaces B.toPre (A ((Dof x).ntw.l i) ∪ A₁ ((Dof x).ntw.l i))
  obtain ⟨B', f', T', h, hf, hpl, hAv, hS', hCoh, hTw⟩ := GlobalTheory.HeightCounting.Up.exists_coh_twFrom hP (w.st x.o.Z) f T.pl _ σ (fun p => A p ∪ A₁ p)
    (fun v hv => P.sub v ((twisted_st x v).1 hv))
    (fun v v' ho hv => (twisted_st x v').2 (hl.2 hT v v' ho ((twisted_st x v).1 hv)))
    (fun i p hp hp' v hv => Finset.mem_coe.2 (Finset.mem_union_right _ (subset_avoidPlaces B.toPre _ hp hp' hv)))
    (fun P g Ξ => S₂ P g Ξ ∪ S₁ P g Ξ) (fun P g Ξ z hz => (Finset.mem_union.1 hz).elim (hS₂ P g Ξ z) (a₁ P g Ξ z))
  obtain ⟨w', hPin, epx, esel, eJ, eδ⟩ := hw' B' f' T' h hf (fun v u hu hA => hAv v u hu (Finset.mem_union_right _ hA))
    fun z hz => hS' z (Finset.mem_union_right _ hz)
  have eP : B'.toPre = B.toPre := h.1
  refine ⟨B', f', T', h, hf, hpl, fun v u hu hA => hAv v u hu (Finset.mem_union_left _ hA),
    fun z hz => hS' z (Finset.mem_union_left _ hz), ⟨⟨w'.δ, w'.exact⟩, eP ▸ hKP.2⟩, fun hq => ?_⟩
  obtain ⟨Z', hX', z', g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hq.1 w' hPin B f T w h hf ⟨b.pin⟩ epx hpl P.Z₀ P.hX P.Wt P.z P.grp
    P.grpAt P.kap ⟨P.exAt, P.inGeo, P.core, P.std⟩ (HoldsL.of_holds P.intersectionNumber_baseChange) P.exact P.sub
    (fun Z' v' hv => (hTw.2 v').2 fun ht => hv _ (below_plUnder h P.Z₀ Z' v') ((twisted_st x _).1 ht))
  have hSt' : Start K B' f' T' w' :=
    ⟨hPin, Or.inr ⟨Z', hX', z', g1, g2, g3, g4, g5.1, g5.2.1, g5.2.2.1, g5.2.2.2, g6, g7⟩, hCoh⟩
  obtain ⟨pre, bare, sa, mt, rat, cu, mv, ck, fin⟩ := hq.2 w' hSt'
  obtain ⟨P', -, eW, g10⟩ := pre Z' hX' z' g1 g2 g3 g4 g5 g6 g7
  have hExt : Ext P.z P'.z := GlobalTheory.T.standardReading_transport_and_extension_trans.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h (enl_refl B') g8 g10
  obtain ⟨x0, hE0, s0⟩ := bare P' (w.st x.o.Z) f eP hf x.fits.grp
  obtain ⟨x1, ⟨la⟩, s1⟩ := sa P' x0 hE0
  obtain ⟨imt⟩ := mt P' x1
  obtain ⟨irat⟩ := rat P' x1 la
  obtain ⟨y, ⟨l2⟩, hcar, hlist⟩ := mv B f T w h hf hSt epx esel eJ eδ P x l.toStrictHenselianAcyclic P' hExt x1
    { toLA := la, mt := imt, rat := irat, cusp := cu P' x1 la } (s0.trans s1)
  have hWt : ∀ v', plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt := fun v' => eW ▸ g9 _ v' (below_plUnder h P.Z₀ Z' v')
  exact ⟨w', hSt', has3_of hP S Γ h x σ (fun i => Finset.subset_union_left) hTw hWt l2 hcar
    ⟨hlist cDep hl.1, fun _ v₁ v₂ ho hv => (hWt v₂).1 (hl.2 hT _ _ (overOne_plUnder_of h P.Z₀ P'.Z₀ ho) ((hWt v₁).2 hv))⟩
    (ck P' y l2) (fin P' y)⟩

theorem second_pass : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → PrN → SerN → DatExt → WeightCaseCondition → GlobalTheory.Published.DiscreteSeriesExists → PhtCmp →
    ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SMt → SRat hL → SCusp hL → ∀ cDep : ℝ, SFinl hL cDep → SFino hL cDep ∧ SecondNo hL cDep :=
  fun hCo hCW hHM hP hS hD hH hds hc _ hMt hRat hCu _ hF => ⟨sFino_of hF, secondNo_of hCo hCW hHM hP hS hD hH hds hc hMt hRat hCu hF⟩

end GlobalTheory.HeightCounting.Up
