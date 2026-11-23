import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteLevelAndSecondStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MinimalKtypeOfLocalComponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SatakeParametersDeterminedAtUnramifiedPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityBoundOfLocalComponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelComparisonChoicesExistAtAllPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTwistedCohomologyClassLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RigidRawPacketEqPow
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick avoidPlaces subset_avoidPlaces)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
theorem goodO_of_alt_alt (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}
    (h : Enl B B') {P : Pre2 K w} (x : St P) {A} (σ : Seed (Dof x) A) (hA : ∀ i, avD (Dof x) (avDesign (Dof x)) i ⊆ A i)
    (hT : TwFrom (w.st x.o.Z) σ h T') {P' : Pre2 K w'} (hW : ∀ v', plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt) {y : St P'} (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL y)
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
  refine ⟨h2, _root_.GlobalTheory.HeightCounting.Rigid.rigid_raw_packet_eq_pow_alt hP (Dof x) (Dof y) (σ.pack (plUnder h v₂)) _ ι χ (cfOf y) l.c.ch l.c.tp v₂ hc.exp hg hF l.c.side.psi h3
    (hs v₂) ((heq_of_eq e1).trans hQ) (e2.trans hk') ((heq_of_eq (congrFun l.c.psi_eq v₂)).trans hχ) fun z hz => ?_⟩
  rw [e2] at hz
  exact hT.1 v₂ z hz
theorem has3_of_carried_levelB2 {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (S : SExt) (Γ : GeoP) {B' : Base} {f' : Fr B'.toPre}
    {T' : TwDat B'} {w' : ColW B' f' T'} (h : Enl B B') {P : Pre2 K w} (x : St P) {A} (σ : Seed (Dof x) A)
    (hA : ∀ i, avD (Dof x) (avDesign (Dof x)) i ⊆ A i) (hT : TwFrom (w.st x.o.Z) σ h T') {P' : Pre2 K w'}
    (hW : ∀ v', plUnder h v' ∈ P.Wt ↔ v' ∈ P'.Wt) {y : St P'} (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL y) (hc : Carried (Dof x) (Dof y)) (hl : ListSt cDep y ∧ SatU P')
    (ck : ∀ s : B'.places.Pl → (Dof y).ntw.Tw, (∀ v, ∃ b, ReadsAt (D := Dof y) (s v) b v) → (∀ v, s (B'.places.conj v) = s v) →
      ∃ c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T'.k T'.psi, c.ch.twI = s)
    (fin : ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL y) (S : SExt) (Γ : GeoP), (ListSt cDep y ∧ SatU P') →
      ∃ (Z : w'.Lt) (v : Lv3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s K w' Z), v.Wt = P'.Wt ∧ Kept l.c.ch v.nch) :
    Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s K B' f' T' w' := by
  have eT : (Dof x).ntw.Tw = (Dof y).ntw.Tw := (same_basic hc.exp.gal hc.exp.set hc.exp.frm).1
  obtain ⟨c, hs⟩ := ck (fun v' => cast eT (σ.s (plUnder h v')))
    (fun v' => (σ.reads (plUnder h v')).imp fun b hb =>
      GlobalTheory.HeightCounting.Up.readsAt_of_plUnder (w.st x.o.Z) (w'.st y.o.Z) h hc v' _ _ b (cast_heq eT _).symm hb)
    (fun v' => congrArg (cast eT) ((congrArg σ.s (TwChar.plUnder_conj h v')).trans (σ.conj _)))
  obtain ⟨Z, v, h1, h2⟩ := fin { toStrictHenselianAcyclic := l, c := c } S Γ hl
  have hg : GoodO (w'.st Z).toD7 v.nch v.xd :=
    _root_.GlobalTheory.HeightCounting.Up.goodO_of_alt_alt hP h x σ hA hT hW { toStrictHenselianAcyclic := l, c := c } hc (fun v' => (heq_of_eq (congrFun hs v')).trans (cast_heq eT _)) h2
      v.nx.2.1.1.1.xd fun v' hv' => h1 ▸ ((TupTieW.tupTied_of_muIsW (w'.st Z) f' T' v.Wt w'.I.xi v.what₂.mu).1 v').1 hv'
  exact ⟨Z, ⟨{ g := v.g, coh := v.coh, Wt := v.Wt, p0 := v.p0, what₂ := v.what₂, rx := v.rx, nch := v.nch, n := v.n, xd := v.xd,
               chiT := v.chiT, nx := ⟨v.nx.1, v.nx.2, ⟨hg⟩⟩ }⟩⟩
theorem secondNo_of_sMt_sRat_sCusp_sFinl (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hS : SerN) (hD : DatExt) (hH : WeightCaseCondition) (hds : GlobalTheory.Published.DiscreteSeriesExists)
    (hc : PhtCmp) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hMt : SMt) (hRat : _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL) (hCu : _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL) {cDep : ℝ}
    (hF : _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep) : _root_.GlobalTheory.HeightCounting.Up.SecondNonvanishing hL cDep := by
  classical
  intro S Γ
  have h3 := GlobalTheory.Mem.R3.Rw.Second.exists_ext_twisted_places hP.greenC hD
  have h4 := (GlobalTheory.T.constructionStartingChoices_of_fine_adelicData GlobalTheory.weilRepresentationUnitaryPair hds hP.hc hP.decay hH).and ((_root_.GlobalTheory.T.bareK_of_discreteSeriesExists hP hds).and ((_root_.GlobalTheory.T.stageAExists_of_inputs_phtCmp hP hc hL).and
    (hMt.and (hRat.and (hCu.and ((_root_.GlobalTheory.T.moveToBase_of_inputs_serN hP hS hL).and ((_root_.GlobalTheory.T.stageCExists_of_casselmanWallach hCo hCW hHM hP hS hL).and (_root_.GlobalTheory.HeightCounting.Up.sFino_of_alt hF))))))))
  refine pass_of (p := fun _ _ _ _ => True) (Step.of_all fun _ _ _ _ _ _ _ h => h) (Step.and h3 h4)
    (EvG.imp GlobalTheory.Mem.Top.ReW.extend_pinned fun K _ _ _ _ hw2 => ?_)
  intro B f T hO hKP hT _ C W V S' N G c₀ hQ hE A S₂ hS₂
  obtain ⟨w, Z, c, ⟨b, -⟩, e⟩ := exists_of_position hQ hE
  have hSt : Start K B f T w := ⟨⟨b.pin⟩, Or.inl hT, b.coh⟩
  obtain ⟨P, x, l, hl, hσ⟩ := _root_.GlobalTheory.HeightCounting.Up.exists_pre_point_with_henselian_level b e
  obtain ⟨A₁, S₁, a₁, hw'⟩ := hw2 B f T w hO ⟨b.pin⟩
  obtain ⟨σ⟩ := hσ fun i => avD (Dof x) (avDesign (Dof x)) i ∪ avoidPlaces B.toPre (A ((Dof x).ntw.l i) ∪ A₁ ((Dof x).ntw.l i))
  obtain ⟨B', f', T', h, hf, hpl, hAv, hS', hCoh, hTw⟩ := _root_.GlobalTheory.HeightCounting.Up.exists_twisted_cohomology_class_lift_alt hP (w.st x.o.Z) f T.pl _ σ (fun p => A p ∪ A₁ p)
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
  exact ⟨w', hSt', _root_.GlobalTheory.HeightCounting.Up.has3_of_carried_levelB2 hP S Γ h x σ (fun i => Finset.subset_union_left) hTw hWt l2 hcar
    ⟨hlist cDep hl.1, fun _ v₁ v₂ ho hv => (hWt v₂).1 (hl.2 hT _ _ (overOne_plUnder_of h P.Z₀ P'.Z₀ ho) ((hWt v₁).2 hv))⟩
    (ck P' y l2) (fin P' y)⟩
theorem sFino_and_secondNo_of_rat_cusp_finl : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → DatExt → WeightCaseCondition → GlobalTheory.Published.DiscreteSeriesExists → PhtCmp →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, SMt → _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL → _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL → ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep → _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.SecondNonvanishing hL cDep :=
  fun hCo hCW hHM hP hS hD hH hds hc _ hMt hRat hCu _ hF => ⟨_root_.GlobalTheory.HeightCounting.Up.sFino_of_alt hF, _root_.GlobalTheory.HeightCounting.Up.secondNo_of_sMt_sRat_sCusp_sFinl hCo hCW hHM hP hS hD hH hds hc hMt hRat hCu hF⟩
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sFino_and_secondNo_of_sFinl' : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → DatExt → WeightCaseCondition → GlobalTheory.Published.DiscreteSeriesExists → PhtCmp → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, SMt → _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL → _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL → ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep → _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.SecondNonvanishing hL cDep := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.sFino_and_secondNo_of_rat_cusp_finl | exact _root_.GlobalTheory.HeightCounting.Up.sFino_and_secondNo_of_rat_cusp_finl | (intros; apply _root_.GlobalTheory.HeightCounting.Up.sFino_and_secondNo_of_rat_cusp_finl <;> assumption)
end
end
