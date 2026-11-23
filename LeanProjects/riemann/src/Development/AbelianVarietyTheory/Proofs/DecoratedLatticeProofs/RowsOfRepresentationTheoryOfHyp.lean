import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharactersMatchBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SeeExJoinPin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConstantsExistForBundleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JoinSubspaceRealDataExistsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLatticesMetricsAgreeOfRealGroupTheoremsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AntiOfStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizesLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraNodesFarApartOfCubicNodeGap
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinned0OfGap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FamAllQ
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.PtRowsAt

section General

open NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe

def Placed {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u} (P : SPack D F0) (S : SRest P) (t : GA D (D.sp.Y 0)) (c : ℝ) : Prop :=
  SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧
    RowJ R eE P.X P.inst P.G t S.j

theorem Placed.of_heq {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {eE : D.what₂.EE →ₗ[ℂ] R.HE.H}
    {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F0 = F0') {P : SPack D F0} {S : SRest P} {P' : SPack D F0'} {S' : SRest P'}
    (hP : HEq P P') (hS : HEq S S') {t : GA D (D.sp.Y 0)} {c : ℝ} (h : Placed R F eE P' S' t c) : Placed R F eE P S t c := by
  subst hF
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hS
  exact h

set_option maxHeartbeats 1000000 in

theorem placed_upd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (k : ℝ) (lam : type_of% R.lam3) (e : type_of% (R.updS k lam).err0) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 D u} (P : SPack D F0) (S : SRest P) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (h : Placed R.toRealDat F.lv2 eE P S t c) :
    Placed ((R.updS k lam).withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 eE P S t c :=
  ⟨⟨h.1.fin, h.1.conj, h.1.mat⟩, h.2.1, h.2.2⟩

set_option maxHeartbeats 1000000 in

theorem exAt_upd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (k : ℝ) (lam : type_of% R.lam3) (e : type_of% (R.updS k lam).err0) (h : R.toRealDat.ExAt) :
    ((R.updS k lam).withErr e).toRealDat.ExAt :=
  ⟨h.ItY, h.ItX, h.ioY, h.ioX, h.Th, h.ioP, h.thF, h.thG⟩

section Args

open GlobalTheory.Mem.Top.Bl

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}

set_option maxHeartbeats 1000000 in

theorem exAt_of_args (a : TwArgs ex t) (x : TwIn ex) (hx : HEq a.x x) : x.R.toRealDat.ExAt := by
  obtain rfl := eq_of_heq hx
  have e := congrArg (fun s => match s with
    | ⟨_, _, _, _, _, _, _, _, _, R, _, _⟩ => R.toRealDat.ExAt) a.pack
  exact e.mpr (exAt_upd _ _ _ _ t.exAt)

set_option maxHeartbeats 1000000 in

theorem placed_of_args (a : TwArgs ex t) (x : TwIn ex) (hx : HEq a.x x)
    {F0 : ∀ u, Formalism.L2.Forms.Forms0 (w.st Z).toD7 u} (P : SPack (w.st Z).toD7 F0) (S : SRest P)
    (g : GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0)) (c : ℝ)
    (h : Placed (D := (w.st Z).toD7) t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y.eE P S g c) :
    Placed x.R.toRealDat x.F.lv2 x.Y.eE P S g c := by
  obtain rfl := eq_of_heq hx
  have e := congrArg (fun s => match s with
    | ⟨_, _, _, _, _, _, _, _, _, R, F, _⟩ => ∀ eE : (w.st Z).toD7.what₂.EE →ₗ[ℂ] R.HE.H, HEq eE t.r.Y.eE →
        Placed R.toRealDat F.lv2 eE P S g c) a.pack
  refine e.mpr (fun eE he => ?_) _ a.eE
  obtain rfl : eE = t.r.Y.eE := eq_of_heq he
  exact placed_upd _ _ _ _ _ _ _ _ _ _ _ _ _ h

end Args

set_option maxHeartbeats 1000000 in

theorem see_join (h5 : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX} (x : TwIn ex) (Rc : Formalism.L2.RecT ex)
    (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (S0 : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (hS : S0 = S.toSTiesR Rc)
    (y : RealIn x Rc S0) (c : ℝ) (hH : Holds x.R x.F) (hP : RealPins (realTOf y))
    (h : Placed x.R.toRealDat x.F.lv2 x.Y.eE P S y.tS c) :
    SeeEx (realTOf y) ∧ Nonempty (Formalism.L2.SG.JoinSI.JoinSI Rc S0 (realTOf y)) := by
  subst hS
  have hSch : SchurAll D := fun V _ S θ M J χ μ 𝓕 =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult h5.2.2.2.1 h5.2.2.2.2 D θ V S M J χ μ 𝓕).2
  have hL := (GlobalTheory.T.rowLattices_metrics_agree_of_realGroupTheorems h5 D _ _ _ _ x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.pins hH).1
  exact ⟨(GlobalTheory.Mem.JPin.seeEx_joinPin _ _ _ _ _ _ _ _ _ x Rc P S y c hH h.1 h.2.1 h.2.2).1,
    (GlobalTheory.T.join_subspace_real_data_exists _ _ _ _ _ _ _ _ _ x Rc P S y c 1 hSch hP hH hH.ok hH.sep hL
      (rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ x).2.1 h.1 h.2.1 h.2.2).1⟩

end General

section Wit

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} {q : Bl.WPt p.s K} {c : ℝ} {b : Bundle (q.w.D q.Z) q.O c}

theorem bundle_pack_eq_adelic_data (w : Bl.BWit q b) : b.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg Bl.RPk.P w.y.eq

theorem dc_of_wit (w : Bl.BWit q b) : DcPtG b.P := by
  rw [bundle_pack_eq_adelic_data w]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).2.2.1

theorem pins_of_wit (w : Bl.BWit q b) : Formalism.IndefR.RealPins b.B.Q := (GlobalTheory.T.characters_match_bundle q b w).2.2.2.2.2.1

theorem frames_of_wit (w : Bl.BWit q b) : Formalism.IndefR.RealT.FramesEx b.B.Q := by
  letI := b.B.alg
  exact GlobalTheory.FramesAtReal.framesEx_of_realisation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b.B.Q (pins_of_wit w)

theorem prim_of_wit (w : Bl.BWit q b) : Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3 := by
  have h : (fun r : Bl.RPk b.R b.S => Formalism.IndefR.Links.PrimRows3 r.B.Q.Rl r.B.Q.F ∧ r.P.A3.fam3.TypesSep3) (Bl.rpkX w.y.y) :=
    ⟨w.y.intersectionNumber_baseChange.prim, w.y.intersectionNumber_baseChange.sep⟩
  rw [← w.y.eq] at h
  exact h

theorem ex_of_wit (w : Bl.BWit q b) : b.B.Q.Rl.toRealDat.ExAt := by
  have h : (fun r : Bl.RPk b.R b.S => r.B.Q.Rl.toRealDat.ExAt) (Bl.rpkX w.y.y) := exAt_of_args w.a w.x w.ax
  rw [← w.y.eq] at h
  exact h

set_option maxHeartbeats 1000000 in

theorem see_join_of_wit (h5 : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) (w : Bl.BWit q b) :
    Formalism.IndefR.SeeEx b.B.Q ∧ Nonempty (Formalism.L2.SG.JoinSI.JoinSI b.R b.S b.B.Q) := by
  obtain ⟨sP, sS, hP, hS, e⟩ := w.s
  have hpin : (fun r : Bl.RPk b.R b.S => Formalism.IndefR.RealPins r.B.Q) (Bl.rpkB b) := pins_of_wit w
  rw [w.y.eq] at hpin
  have h0 := placed_of_args w.a w.x w.ax q.sat.P q.sat.S q.sat.t q.sat.c ⟨q.sat.see, q.sat.ev, q.sat.rowJ⟩
  have ht : w.y.y.tS = q.sat.t := eq_of_heq w.pt.1
  have hF : (fun u => (b.R.T.cols.forms u).to0) = fun u => (q.x.col.C.forms u).to0 :=
    congrArg (fun C : type_of% q.x.col.C => fun u => (C.forms u).to0) w.recPin.s.cols
  have h1 := Placed.of_heq hF hP hS h0
  rw [← ht] at h1
  have h : (fun r : Bl.RPk b.R b.S => Formalism.IndefR.SeeEx r.B.Q ∧ Nonempty (Formalism.L2.SG.JoinSI.JoinSI b.R b.S r.B.Q)) (Bl.rpkX w.y.y) :=
    see_join h5 w.x b.R sP sS b.S e w.y.y q.sat.c w.y.intersectionNumber_baseChange hpin h1
  rw [← w.y.eq] at h
  exact h

end Wit

theorem gapHyp_of_hd {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hCl : 1801 ≤ Cl) (H : GlobalTheory.Core.Rk.HD D L C' Cl Cg cb Cu cT CT) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  have HL := H.2.2.1
  obtain ⟨hS, hr⟩ := GlobalTheory.Core.Rk.HdGap.scale_of hCl HL
  have hr0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  refine ⟨hr, fun τ j hj => ?_⟩
  have := GlobalTheory.Core.Rk.HdGap.gap_of HL τ j.1 hj
  simp only [Fin.eta] at this
  have key : (((16 : ℚ) * (D.R.r : ℚ) ^ 19 : ℚ) : ℝ) ≤
      (((D.hc τ).b ⟨j.1 + 1, hj⟩ - (D.hc τ).b j : ℚ) : ℝ) := by
    rw [Rat.cast_sub]; push_cast; linarith
  exact_mod_cast key

theorem ptRows_at_member : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ _ _ _ b => PtRows b) := by
  intro h1 h2 h3 h4 h5 hL p
  obtain ⟨Cl₀, hnc⟩ := GlobalTheory.Core.Rk.HdNc.hd_nc
  refine (GlobalTheory.T.constants_exist_for_bundle hL p (fun _ _ => 0) (fun _ _ => max 1801 Cl₀) (fun _ _ => 0)).imp ?_
  rintro κ K β c b - - ⟨q, b', ⟨w⟩, he⟩ ⟨C', Cl, Cg, CT, -, hCl, -, hHD, -, -, hB, hrS⟩
  have key : ∀ s t : (Σ (D : D7) (O : Obj D), Bundle D O c), s = t →
      (Nonempty (Formalism.L2.SG.JoinSI.JoinSI t.2.2.R t.2.2.S t.2.2.B.Q) ∧ DcPtG t.2.2.P ∧ Formalism.IndefR.RealT.FramesEx t.2.2.B.Q ∧
        Formalism.IndefR.SeeEx t.2.2.B.Q ∧ t.2.2.B.Q.Rl.toRealDat.ExAt ∧
        (Formalism.IndefR.Links.PrimRows3 t.2.2.B.Q.Rl t.2.2.B.Q.F ∧ t.2.2.P.A3.fam3.TypesSep3)) →
      (Nonempty (Formalism.L2.SG.JoinSI.JoinSI s.2.2.R s.2.2.S s.2.2.B.Q) ∧ DcPtG s.2.2.P ∧ Formalism.IndefR.RealT.FramesEx s.2.2.B.Q ∧
        Formalism.IndefR.SeeEx s.2.2.B.Q ∧ s.2.2.B.Q.Rl.toRealDat.ExAt ∧
        (Formalism.IndefR.Links.PrimRows3 s.2.2.B.Q.Rl s.2.2.B.Q.F ∧ s.2.2.P.A3.fam3.TypesSep3)) := by
    rintro _ _ rfl h
    exact h
  have hsj := see_join_of_wit ⟨h1, h2, h3, h4, h5⟩ w
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := key ⟨β.D, β.O, b⟩ ⟨q.w.D q.Z, q.O, b'⟩ he
    ⟨hsj.2, dc_of_wit w, frames_of_wit w, hsj.1, ex_of_wit w, prim_of_wit w⟩
  exact ⟨a1, a2, a3, a4, a5, a6,
    GlobalTheory.Core.Rk.finX_of_gap _ b.S.toSTies (gapHyp_of_hd ((le_max_left _ _).trans hCl) hHD),
    hnc _ _ _ _ _ _ _ _ _ ((le_max_right _ _).trans hCl) hHD b.S.X,
    GlobalTheory.Core.Rk.GapOfNodes.harishChandraNodesFarApart_of_cubic_node_gap _ hB, hrS⟩

end GlobalTheory.Fam.PtRowsAt

end
