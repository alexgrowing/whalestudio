import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementProperty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Placed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedBy
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotOfPlacedByStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColLevelMatchFamStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZeroMem
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
set_option maxHeartbeats 1000000 in
theorem conj_mem_K_two_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) {v : VCom f.c} (G : (_root_.GlobalTheory.BaseChain.com_z W).Pg → GLoc v)
    (hBot : GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hBl : B.lev = f.c.B 0 D.R.rS h0) (hAd : B.Adapted (W.S.tr u).wt) (hTr : _root_.GlobalTheory.MiTop.LevTraceAlt f B)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧
      finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (hone : ∀ k ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W),
      (∀ PP ∈ (_root_.GlobalTheory.BaseChain.com_z W).Pg, redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP (finE (D.sp.Y 0) k) = 1) →
      (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2) :
    ∀ k ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W), (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2 := by
  have hemb : ∀ b, embA B.d B.o b = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o b : GA D (D.sp.Y 0)) := fun b =>
    by
      have h1 := congr_arg_heq (fun L : BesLev D D.R.rS => (embA L.d L.o : GA D L.A →* GA D L.V)) hBl
      have h2 : embA B.d B.o = (embA (f.c.bes 0 D.R.rS h0).d (f.c.bes 0 D.R.rS h0).o : GA D (D.sp.X 0) →* GA D (D.sp.Y 0)) :=
        eq_of_heq h1
      exact DFunLike.congr_fun h2 b
  have hfl : flagN B.d = (flagN (f.c.bes 0 D.R.rS h0).d : Subgroup (GA D (D.sp.Y 0))) :=
    eq_of_heq (congr_arg_heq (fun L : BesLev D D.R.rS => flagN L.d) hBl)
  refine GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G h0 hBot
    (fun k : GA D (D.sp.Y 0) => (iotaX W.S.X W.Q.instEq (s * k * s⁻¹)).2 ∈ W.S.X.K2) ?_ ?_ ?_ hone
  · intro (k : GA D (D.sp.Y 0)) _ (k' : GA D (D.sp.Y 0)) _ q q'
    show (iotaX W.S.X W.Q.instEq (s * (k * k') * s⁻¹)).2 ∈ W.S.X.K2
    have e : s * (k * k') * s⁻¹ = (s * k * s⁻¹) * (s * k' * s⁻¹) := by group
    rw [e, map_mul, Prod.snd_mul]
    exact W.S.Y.hK.2.1 _ q _ q'
  · intro PP (n : GA D (D.sp.Y 0)) q hn _ _ hk
    have hn' : n ∈ flagN B.d := by rw [hfl]; exact hn
    have e : s * (t⁻¹ * n * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        (embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      rw [hs]; group
    have hk' : t⁻¹ * n * t ∈ levS (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) := by rw [ht]; exact hk
    have hKs := ((hSt (s * (t⁻¹ * n * t) * s⁻¹)).1 ⟨GlobalTheory.MemMatch.conj_mem_GfC W.S.X W.Q.instEq s _ hk'.1, by
      rw [map_mul, map_mul, map_inv, GlobalTheory.FrameConj.conj_mem_St_iff]; exact parLev_St hk'.2.1⟩).2
    have hN := ((B.tieN _).1 (GlobalTheory.CharLaws.embA_conj_mem B.d B.o (a₀ * a) hn')).2
    have goal : (iotaX W.S.X W.Q.instEq (s * (t⁻¹ * n * t) * s⁻¹)).2 ∈ W.S.X.K2 := by
      rw [e] at hKs ⊢
      generalize embA B.d B.o (a₀ * a) * n * (embA B.d B.o (a₀ * a))⁻¹ = n' at hN hKs ⊢
      rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply] at hKs ⊢
      generalize iotaX W.S.X W.Q.instEq n' = y at hN hKs ⊢
      change (W.S.X.xu u)⁻¹ * y.2 * W.S.X.xu u ∈ _ at hKs ⊢
      refine Formalism.L2.SG.Pf.unipotent_conj_mem_level hN ?_
      have := Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (Formalism.L2.SG.Pf.unitaryCongruence.K_mul _ (W.S.X.xu_K u) hKs)
        (Formalism.L2.SG.Pf.unitaryCongruence.K_inv _ (W.S.X.xu_K u))
      rwa [show W.S.X.xu u * ((W.S.X.xu u)⁻¹ * y.2 * W.S.X.xu u) * (W.S.X.xu u)⁻¹ = y.2 by group] at this
    subst ht
    exact goal
  · intro b hb hk
    rw [← hemb b] at hk
    have h1 := (_root_.GlobalTheory.T.level_trace_adapted_translate_alt W hPk u f B hTr hAd a₀ hH0 b hb).1.1 hk
    have hab : a * b * a⁻¹ = b := by rw [← Subgroup.mem_center_iff.1 hac b]; group
    have e : s * (t⁻¹ * embA B.d B.o b * t) * s⁻¹ = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
        embA B.d B.o (a₀ * b * a₀⁻¹) * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      have : a₀ * b * a₀⁻¹ = (a₀ * a) * b * (a₀ * a)⁻¹ := by
        conv_lhs => rw [← hab]
        group
      rw [this, map_mul _ _ (a₀ * a)⁻¹, map_mul _ (a₀ * a) b, map_inv, hs]; group
    rw [← e] at h1
    rw [← hemb b]
    subst ht
    exact h1.2
set_option maxHeartbeats 2000000 in
theorem mem_K_two_iff_of_family_character (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) {v : VCom f.c} (G : (_root_.GlobalTheory.BaseChain.com_z W).Pg → GLoc v)
    (hBot : GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G)
    (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hBl : B.lev = f.c.B 0 D.R.rS h0) (hAd : B.Adapted (W.S.tr u).wt) (hTr : _root_.GlobalTheory.MiTop.LevTraceAlt f B)
    (a₀ : GA D (D.sp.X 0)) (hH0 : IsTransportAdelicCorrection (W.S.tr u) a₀) (a : GA D (D.sp.X 0)) (hac : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (t s : GA D (D.sp.Y 0)) (ht : t = f.g.b 0)
    (hs : s = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * t)
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧
      finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) ↔
      ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset))
    (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ GfC (D.sp.Y 0))
    (hκS : finE (D.sp.Y 0) κ ∈ St (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0))) :
    (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.K2 ↔
      rTup (F := D.host.F) (E := D.host.E) (finE (D.sp.Y 0) s * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0)) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈
        (_root_.GlobalTheory.LevZero.datZero_alt W).P.H := by
  obtain ⟨hr, ξ, hL⟩ := hBot.mem.lev
  obtain ⟨N, hN, -⟩ := hBot.mem.base
  have hrk : (D.sp.Y 0).rank = D.R.rankY 0 := hBot.mem.rank
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by rw [hrk]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hr' : D.R.r ≤ (D.sp.Y 0).rank := hr
  have hLb : _root_.GlobalTheory.LevZero.datZero_alt W = (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' (_root_.GlobalTheory.BaseChain.com_z W).Pg ∅
      (_root_.GlobalTheory.BaseChain.com_z W).P (_root_.GlobalTheory.BaseChain.com_z W).chi ξ Frm.B) := hL
  have hlift : Lev.LiftsExist (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) (_root_.GlobalTheory.LevZero.datZero_alt W) :=
    GlobalTheory.ChainOnto.FlagAct.liftsExist_stage hBot.com hBot.mem
  obtain ⟨m, hm⟩ := GlobalTheory.MemMatch.exists_read W.S.X W.Q.instEq (_root_.GlobalTheory.BaseChain.com_z W).Pg hBot.typ hBot.com.split
    (fun PP => ⟨_, (hBot.loc PP).idem⟩) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) N hN s hSt
  have hin := _root_.GlobalTheory.LevZeroMem.conj_mem_K_two_alt W hPk f B G hBot h0 hBl hAd hTr a₀ hH0 a hac t s ht hs hSt (fun k hk h1 =>
    (hm k hk.1 (parLev_St hk.2.1)).2 fun PP => by rw [h1 PP.1 PP.2, mul_one, mul_inv_cancel]; exact one_mem _)
  have hpat : ∀ g : ∀ PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg, GL (Fin D.R.r) (kP PP.1),
      g ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H ↔ ∀ PP, GlobalTheory.SymRes.IsPat D.R.rS D.R.k (g PP) :=
    fun g => (hBot.grp g).trans (forall_congr' fun PP => GlobalTheory.LevZero.exists_red_iff_isPat (G PP) PP.1 (hBot.loc PP).idem (g PP))
  rw [hLb] at hlift hin ⊢
  have hlev : ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St (F := D.host.F) (E := D.host.E) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) →
      (fun PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg => upperLeftBlock hr' (redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k))) ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H →
      k ∈ levS (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) (datY (D.sp.Y 0).rank D.R.r D.R.t 0 hr' (_root_.GlobalTheory.BaseChain.com_z W).Pg ∅
        (_root_.GlobalTheory.BaseChain.com_z W).P (_root_.GlobalTheory.BaseChain.com_z W).chi ξ Frm.B) := by
    intro k hk hS hP
    refine ⟨hk, ?_⟩
    show finE (D.sp.Y 0) k ∈ lev _ _ _ _
    rw [mem_lev, mem_parLev]
    exact ⟨⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hS, fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _,
      fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, hP⟩
  obtain ⟨k₀, rfl⟩ : ∃ k₀, κ = s * k₀ * s⁻¹ := ⟨s⁻¹ * κ * s, by group⟩
  have hk₀ : k₀ ∈ GfC (D.sp.Y 0) := by
    have := GlobalTheory.MemMatch.conj_mem_GfC W.S.X W.Q.instEq s⁻¹ _ hκ
    rwa [show s⁻¹ * (s * k₀ * s⁻¹) * s⁻¹⁻¹ = k₀ by group] at this
  have hfe : finE (D.sp.Y 0) (s * k₀ * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k₀ * (finE (D.sp.Y 0) s)⁻¹ := by rw [map_mul, map_mul, map_inv]
  rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at hκS
  rw [hfe, GlobalTheory.FrameConj.rTup_conj]
  refine ⟨fun hK => ?_, fun hP => hin k₀ (hlev k₀ hk₀ hκS hP)⟩
  refine (hpat _).2 fun PP => (GlobalTheory.MemMatch.isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 ?_
  haveI : Finite (kP PP.1) := Ideal.finiteQuotientOfFreeOfNeBot PP.1.asIdeal PP.1.ne_bot
  have hrr : (D.sp.Y 0).rank = D.R.k + (2 * D.R.rS + 1) := by
    have := le_antisymm hn hr'
    have h0' := h0
    unfold Ranks.r at this
    omega
  refine GlobalTheory.SymResCount.conj_pat_onto (kP PP.1) _ D.R.rS D.R.k hrr (m PP) (fun g hg => ?_) _ ((hm k₀ hk₀ hκS).1 hK PP)
  let g0 : ∀ Q : (_root_.GlobalTheory.BaseChain.com_z W).Pg, GL (Fin D.R.r) (kP Q.1) := Function.update (fun _ => 1) PP (upperLeftBlock hr' g)
  have hg0 : g0 ∈ (_root_.GlobalTheory.BaseChain.com_z W).P.H := (hpat _).2 fun Q => by
    by_cases hQ : Q = PP
    · subst hQ
      simp only [g0, Function.update_self]
      exact (GlobalTheory.MemMatch.isIdentityOffFreePositions_rightBlock_iff _ _ hr' hn _).2 hg
    · simp only [g0, Function.update_of_ne hQ]
      exact GlobalTheory.SymRes.isPat_one _ _
  obtain ⟨k, hk, hkp, hkr⟩ := hlift g0
  have hkr' : (fun PP : (_root_.GlobalTheory.BaseChain.com_z W).Pg => upperLeftBlock hr' (redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k))) = g0 := hkr
  have h1 := (hm k hk (parLev_St hkp)).1 (hin k (hlev k hk (parLev_St hkp) (hkr' ▸ hg0))) PP
  have h2 : redFn (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (_root_.GlobalTheory.Fam.pk_z W).βY 0) PP.1 (finE (D.sp.Y 0) k) = g :=
    GlobalTheory.MemMatch.reductionBlock_injective_of_eq hr' hn _ _ ((congrFun hkr' PP).trans (Function.update_self _ _ _))
  rwa [h2] at h1
set_option maxHeartbeats 2000000 in
theorem mem_rowJ_iff_rTup_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → (κ ∈ rowJ W.S.X W.Q.instEq ↔ Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H) := by
  intro D L hT Gi Gl Kc Yd cX ex W hPk u f B hPl a₀ hH0 a _ hac hStab κ hκ hκS
  obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, hc, hv, hvt, hsh, hpin, hread, hbt⟩ := hPl
  have hBot := _root_.GlobalTheory.T.bessel_local_type_data_alt W hPk u f B k ι v o n G pl ⟨hc, hv, hvt, hsh, hpin, hread, hbt⟩
  have h0 := h0_eq D
  have hκ1 : (iotaX W.S.X W.Q.instEq κ).1 = 1 := (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq κ).2 hκ
  show (iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.K2 ↔ _
  exact (and_iff_right hκ1).trans (_root_.GlobalTheory.LevZeroMem.mem_K_two_iff_of_family_character W hPk f B _ hBot h0 (hbt.lev h0) hbt.adapted hbt.trace a₀ hH0 a hac _ _ rfl rfl
    hStab κ hκ hκS)
end GlobalTheory.LevZeroMem
end
end
