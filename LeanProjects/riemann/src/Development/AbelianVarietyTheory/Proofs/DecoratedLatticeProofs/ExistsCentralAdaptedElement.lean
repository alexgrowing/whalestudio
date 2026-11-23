import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabMatch
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCore
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLocalTypeData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulMulDivCancelLeft
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedLatticeIndexZeroNormalFrameComponentStatement
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

def Facts {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} (o : TDat c k ι) {n : ℕ} (G : Fin n → GLoc v) (Lm : Lat (c.V 0)) (b : BesAt (c.V 0) (c.X 0) D.R.rS) : Prop :=
  ∃ M : Lat b.V₀,
    (∀ p, IsSelfDualC b.V₀ M ∧ MonoAt b.d (v.N 0) M p ∧ PrimAt c.ψ b.d (v.N 0) p ∧ LastAt c.ψ b.d (vecB b.o b.ζ) (v.N 0) M p) ∧
    (∀ p, p ∉ v.tP → ∃ LL, IsSelfDualC b.L LL ∧ OrthAt b.o M (c.x 0).L LL p) ∧
    (∀ i, ∃ β₀ : GlobalTheory.FinPl.Frame (o.p i) b.V₀ (Fin (c.X 0).rank ⊕ Fin 1), IsSumFrame b.o b.ζ (o.β 0 i) β₀ ∧
      β₀.IsLat M (GlobalTheory.LatPair.gluedS o.q 1 (o.Q 0 i).ker (o.Q 0 i).vec)) ∧
    ∀ i, valuation (G i).k ((G i).q.pr (incA D (star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ))) = 1 ∧
      WShape (G i).q b.d b.o b.ζ Lm (fun j => ((((G i).S.ϖ : (G i).kˣ) : (G i).k) ^ (j.1 + 1))⁻¹)
        (fun j => ((((G i).S.ϖ : (G i).kˣ) : (G i).k) ^ (2 * D.R.rS - j.1 + 1))⁻¹)
        (((((G i).S.ϖ : (G i).kˣ) : (G i).k) ^ (D.R.rS + 1))⁻¹) 1 (c.x 0).L

theorem facts {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} (o : TDat c k ι) {n : ℕ} (G : Fin n → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (hc : c.Is) (hS : ShapeOff v o)
    (PP : Fin n → Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D))
    (hloc : ∀ i, LocAt (G i) (PP i) b β) (Λ Lm : Lat (c.V 0)) (hfr : Formalism.L2.DIV.IsFrame β Λ) (hmv : ∀ P, Moves (c.V 0) b Λ Lm P) :
    Facts o G Lm (c.bes 0 D.R.rS h0) :=
  ⟨o.M 0 _ h0, fun p => ⟨((hS.good p).bf 0 _ h0).sdV₀, ((hS.good p).bf 0 _ h0).monoV, ((hS.good p).bf 0 _ h0).prim,
      GlobalTheory.T.lastWittLine_of_besselJacobiLatticesGood D _ hc.std _ _ _ _ _ _ _ p ((hS.good p).bf 0 _ h0)⟩,
    fun p hp => (hS.split p hp).core 0 _ h0, fun i => ⟨_, (hS.glued 0 _ h0 i).sum, (hS.glued 0 _ h0 i).lat⟩,
    fun i => ⟨(G i).hz_unit 0 _ h0, GlobalTheory.LevZero.wShape_of_besFrame_loc (G i) _ h0 Lm
      (GlobalTheory.T.movedLattice_indexZero_normalFrame_component (G i) (PP i) b β (hloc i) ((G i).s + 1) (zero_add _) Λ Lm hfr (hmv _))⟩⟩

theorem sMoves_of_moves {S : HSp D} {t g : GA D S} {Λ L L' M : Lat S} {p : GlobalTheory.FinPl.Pl D} {c : AE D}
    (h : Moves S t Λ L (· = p)) (h' : Moves S t Λ L' (· = p)) (hs : SMoves S c g L M p) : SMoves S c g L' M p := by
  intro y hy
  have := moves_trans (moves_symm h') h y hy
  rw [mul_inv_cancel, mt_one', Matrix.one_mulVec] at this
  exact this.trans (hs y hy)

set_option maxHeartbeats 2000000 in

theorem stab_match : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B → Framed B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ GlobalTheory.LevZero.StabAt f B a₀ a := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hPl hFr a₀ ha₀
  obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, hc, hv, hVT, hSh, hGP, hGR, hBT⟩ := hPl
  have hbot := GlobalTheory.LevZero.bot_of_placedBy W hW u f B k ι v o n G pl ⟨hc, hv, hVT, hSh, hGP, hGR, hBT⟩
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
  have hΛ : IsSelfDualC (Yc D 0) ((pk W).ΛY 0) := hbot.mem.selfDual
  have hfr : Formalism.L2.DIV.IsFrame ((pk W).βY 0) ((pk W).ΛY 0) := hbot.mem.frame
  obtain ⟨Lm, hLm, hmv⟩ := GlobalTheory.FinPl.GlobImage.image_moves (Yc D 0) ((pk W).ΛY 0) hΛ (f.g.b 0)
  have hloc : ∀ i, LocAt (G i) (pl i).1 (f.g.b 0) ((pk W).βY 0) := fun i => by
    have := hbot.loc (pl i)
    rwa [Equiv.symm_apply_apply] at this
  have hC := facts o G h0 hc hSh (fun i => (pl i).1) (f.g.b 0) ((pk W).βY 0) hloc ((pk W).ΛY 0) Lm hfr hmv
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
      have hpS : p ∉ (GlobalTheory.BaseChain.com W).S := by
        intro h
        obtain ⟨PP, h1, h2⟩ := Finset.mem_image.1 h
        exact hpg ((hVT.gP p).2 ⟨PP, h1, h2.symm⟩)
      have hN : Moves (Yc D 0) (f.g.b 0) ((pk W).ΛY 0) (v.N 0) (· = p) := hVT.moves 0 hm _ fun p' hp' => hp' ▸ hpg
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
        obtain ⟨y, hy, hU⟩ := GlobalTheory.T.columnLevel_iff_rowLattice_kept_at_place D W.S.X W.Q.instEq u W.Q.Rl.ψ (F0 W u) (W.S.tr u) W.S.Y.hK B a₀ hE hLM hBa ha₀ _ hg a ha
        have c5 : (y : GL _ _) ∈ (F0 W u).cls0.lev.U ↔ Moves (D.sp.Y 0) (embA B.d B.o a) (v.N 0) (v.N 0) (· = (o.p i).v) :=
          (hBT.trace a (mem_GfC_of_grpAt ha) y hy).1.trans
            ((GlobalTheory.T.mem_chainLevel_iff_carriesLattice_offLevel D (GlobalTheory.BaseChain.com W) 0 (stZero W).st hbot.mem _ hpS _
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
  exact ⟨a, haf, hac, stab_of_frame W.S.X W.Q.instEq u ((pk W).βY 0) _ _ z hz
    (GlobalTheory.T.isFrame_finitePart_mul_of_carries_lattice D (D.sp.Y 0) _ ((pk W).ΛY 0) (latS D) ((pk W).βY 0) (moves_trans (hmv _) hmvz) hfr)⟩

end GlobalTheory.LevZero.StabMatch

end
