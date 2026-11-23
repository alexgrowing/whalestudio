import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralAdaptedElement
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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotOfPlacedBy
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.Core.Mi.LatMatch
noncomputable section
namespace GlobalTheory.LevZero.StabMatch
variable {D : D7}
set_option maxHeartbeats 2000000 in
theorem exists_center_stab_at_of_transport_correction : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → Framed B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hPl hFr a₀ ha₀
  obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, hc, hv, hVT, hSh, hGP, hGR, hBT⟩ := hPl
  have hbot := _root_.GlobalTheory.LevZero.bot_of_placedBy_alt W hW u f B k ι v o n G pl ⟨hc, hv, hVT, hSh, hGP, hGR, hBT⟩
  obtain ⟨μ, lam, hμ, hl, hz', he, he'⟩ := hFr
  have hF : B.FrameAt μ lam :=
    ⟨hμ, hl, funext fun r => funext fun a => he r a, funext fun r => funext fun a => he' r a, funext fun r => hz' r⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by have := D.R.rS_two; omega
  have hm : 0 < D.R.m := by omega
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hW.bot.idE
  have hLM := hW.bot.hyp.2.1 u
  have hBa := hBT.adapted
  have hψ : IsStdChar D W.Q.Rl.ψ (-1) := hc.std
  have hb : @Eq (BesAt (f.c.V 0) (f.c.X 0) D.R.rS) (f.c.bes 0 D.R.rS h0) (toBes B) := eq_toBes B _ _ (hBT.lev h0)
  have hΛ : IsSelfDualC (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) := hbot.mem.selfDual
  have hfr : Formalism.L2.DIV.IsFrame ((_root_.GlobalTheory.Fam.pk_z W).βY 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) := hbot.mem.frame
  obtain ⟨Lm, hLm, hmv⟩ := GlobalTheory.FinPl.GlobImage.image_moves (Yc D 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) hΛ (f.g.b 0)
  have hloc : ∀ i, LocAt (G i) (pl i).1 (f.g.b 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) := fun i => by
    have := hbot.loc (pl i)
    rwa [Equiv.symm_apply_apply] at this
  have hC := facts o G h0 hc hSh (fun i => (pl i).1) (f.g.b 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) hloc ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) Lm hfr hmv
  rw [hb] at hC
  obtain ⟨M, c1, c2, c3, c4⟩ := hC
  obtain ⟨s1, s2, s3, -, -, s6⟩ := rows_shape hE hF
  obtain ⟨-, z2, -⟩ := GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm D W.S.X W.Q.instEq u W.Q.Rl.ψ _ B μ lam hE hF
  have loc : ∀ p : GlobalTheory.FinPl.Pl D, ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) p a ∧ NormOneAt p c ∧
      SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) Lm (latS D) p := by
    intro p
    by_cases hpg : p ∈ v.gP
    · obtain ⟨i, rfl⟩ := (hGP.places p).1 hpg
      have hpT : (G i).q.v ∉ v.tP := Finset.disjoint_left.1 hv.disj hpg
      obtain ⟨q⟩ : Nonempty (GlobalTheory.LatPair.Unif (G i).k) := inferInstance
      have hϖ := (GlobalTheory.SeeSaw.LevelTest.val_eq_unif (G i).q (hloc i).idem q (hbot.typ.1 (pl i).1 (pl i).2)
        (GlobalTheory.SeeSaw.LevelTest.g_notMem_sq (pl i).1)).trans (GlobalTheory.SeeSaw.LevelTest.unif_val q (G i).S.unif)
      exact loc_level hE hF hLM hBa ha₀ (G i).q (G i).unit _ (by simpa using hϖ) (fun h => hpT ((hVT.tP _).2 h))
        (c4 i).1 hLm (hBT.lat _ hpT) (c4 i).2
    · have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal := by
        intro h
        obtain ⟨PP, ⟨h1, h2⟩, -⟩ := hbot.typ.2 p h
        exact hpg ((hVT.gP p).2 ⟨PP, h1, h2.symm⟩)
      have hpS : p ∉ (_root_.GlobalTheory.BaseChain.com_z W).S := by
        intro h
        obtain ⟨PP, h1, h2⟩ := Finset.mem_image.1 h
        exact hpg ((hVT.gP p).2 ⟨PP, h1, h2.symm⟩)
      have hN : Moves (Yc D 0) (f.g.b 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (v.N 0) (· = p) := hVT.moves 0 hm _ fun p' hp' => hp' ▸ hpg
      obtain ⟨d1, d2, d3, d4⟩ := c1 p
      suffices H : ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) p a ∧ NormOneAt p c ∧
          SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) (v.N 0) (latS D) p by
        obtain ⟨a, c, h1, h2, h3⟩ := H
        exact ⟨a, c, h1, h2, sMoves_of_moves (S := D.sp.Y 0) hN (hmv _) h3⟩
      refine loc_of_core hψ hE hF hg (hv.sd 0 hm) d1 d2 d3 d4 ?_
      by_cases hpT : p ∈ v.tP
      · have hTv := (hVT.tP p).1 hpT
        obtain ⟨i, rfl⟩ := (hSh.pre.tP p).1 hpT
        obtain ⟨β₀, e1, e2⟩ := c3 i
        have hr : 3 ≤ Fintype.card (Fin (D.sp.X 0).rank) := by
          have h1 := D.R.m_add_three_le_k
          rw [Fintype.card_fin, D.sp.X_rank 0 (Nat.zero_le _), Ranks.N]
          omega
        refine GlobalTheory.T.exists_central_element_homothetic_gluedCores D k (o.p i) _ _ _ B.o B.ζ _ (o.β 0 i) β₀ M _ μ _ o.q (o.Q 0 i) a₀ hr e1 d1 s2 e2 hF.ne (s6 _) z2
          (GlobalTheory.SeeSaw.LevelTest.unifT_of _ _ hTv) fun a ha => ?_
        obtain ⟨y, hy, hU⟩ := GlobalTheory.T.columnLevel_iff_rowLattice_kept_at_place D W.S.X W.Q.instEq u W.Q.Rl.ψ (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) W.S.Y.hK B a₀ hE hLM hBa ha₀ _ hg a ha
        have c5 : (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔ Moves (D.sp.Y 0) (embA B.d B.o a) (v.N 0) (v.N 0) (· = (o.p i).v) :=
          (hBT.trace a (mem_GfC_of_grpAt ha) y hy).1.trans
            ((GlobalTheory.T.mem_chainLevel_iff_carriesLattice_offLevel D (_root_.GlobalTheory.BaseChain.com_z W) 0 (_root_.GlobalTheory.LevZero.levelZeroState W).st hbot.mem _ hpS _
              (conj_mem_grpAt (S := D.sp.Y 0) (embA_mem_grpAt _ _ ha) _)).trans (moves_conj (S := D.sp.Y 0) hN _))
        exact ((GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises D _ _ _ B.d _ _ _ _ d2).symm.trans (c5.symm.trans hU)).trans
          (GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises D _ _ _ B.d _ _ _ _ (s3 _))
      · obtain ⟨LL, e1, e2⟩ := c2 p hpT
        have hTv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal := fun h => hpT ((hVT.tP p).2 h)
        exact GlobalTheory.T.orthogonalSumCores_homothetic_off_level D _ _ _ B.o B.ζ M _ (f.g.x 0).L LL μ _ p a₀ B.line e1 e2
          (rows_trace hE hF hLM hBa ha₀ p (hBT.lat p hpT))
          (GlobalTheory.T.selfDualLattice_splitsOff_unitNormLine_at_place D _ _ _ B.o B.ζ _ μ _ p B.line s2 hF.ne (s6 p) z2 hTv) hF.ne (s6 p) z2 hTv
  obtain ⟨a, haf, hac, z, hz, hmvz⟩ := GlobalTheory.T.exists_central_glue_localHomotheties D (D.sp.Y 0) (D.sp.X 0) (embA B.d B.o) (embA B.d B.o a₀) Lm
    (latS D) hLm s1 (fun v a ha => embA_mem_grpAt _ _ ha) (fun v => by simpa only [map_mul] using loc v)
  rw [← map_mul] at hmvz
  exact ⟨a, haf, hac, stab_of_frame W.S.X W.Q.instEq u ((_root_.GlobalTheory.Fam.pk_z W).βY 0) _ _ z hz
    (GlobalTheory.T.isFrame_finitePart_mul_of_carries_lattice D (D.sp.Y 0) _ ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (latS D) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) (moves_trans (hmv _) hmvz) hfr)⟩
end GlobalTheory.LevZero.StabMatch
end
end
