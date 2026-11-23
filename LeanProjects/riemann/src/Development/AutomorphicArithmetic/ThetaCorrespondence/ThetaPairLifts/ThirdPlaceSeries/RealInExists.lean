import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedRealizationGeometric
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.R3.TwIn.grp GlobalTheory.Mem.R3.TwIn.fin GlobalTheory.Mem.R3.TwIn.alg
namespace GlobalTheory.Mem.R3.SelRealIn
open Formalism.L2.SG.RowsJoinPinned Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta GlobalTheory.Mem.Top.Bl
section Gen
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Gen
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
theorem psi_eq_theta_psi_of_recPin (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex) (h : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R) (x : TwIn q.O.ex) :
    x.R.ψ = R.T.theta.W.ψ := by
  have h1 := x.pins.keep.std
  have h2 := q.x.th.std
  have e := h.s.theta
  have h3 : Formalism.L2.Theta.IsStdChar (q.w.D q.Z) R.T.theta.W.ψ (-1) :=
    (congrArg (fun z : (Σ a, Formalism.L2.Theta.AllTied (q.w.D q.Z) q.O.ex.th a) => Formalism.L2.Theta.IsStdChar (q.w.D q.Z) z.2.W.ψ (-1)) e).mpr h2
  exact GlobalTheory.StdAdelicChar.isStdChar_unique h1 h3
set_option maxHeartbeats 4000000 in
theorem exists_ratDat_nExpRealS (q : WPt p.s K) (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex) (hx : HEq a.x x) :
    ∃ (Sx : Formalism.IndefR.NX.RatDat (q.w.D q.Z).ntw) (n : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx),
      HEq Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core_data_of_point.row.kKs q.core_data_of_point.row.hk) ∧
      HEq n.eF q.core_data_of_point.row.nexp.eF ∧ HEq n.fi q.core_data_of_point.row.nexp.fi := by
  obtain rfl : a.x = x := eq_of_heq hx
  obtain ⟨Dc, Sp, Zsc, lam, err, _, x, pack, _⟩ := a
  obtain ⟨G, Pl0, I0, T0, A3, core, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  have h := nexp_upd (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG _ q.core_data_of_point.row.nexp lam err
  exact (by with_unfolding_all exact (h :))
set_option maxHeartbeats 4000000 in
theorem realIn_exists_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toRealSpectralMatching R).X u (sS.toRealSpectralMatching R).Y.hK), HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := (sS.toRealSpectralMatching R).X) (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) (sS.toRealSpectralMatching R).Y.hK (sS.toRealSpectralMatching R).G x.wd (fun m => _root_.Formalism.IndefR.pwOf_alt (sS.toRealSpectralMatching R) hin (x.wd m)) x.bR) → ∀ (κ : ℝ) (sEEc : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX (sS.toRealSpectralMatching R).X)), HEq x.sEE sEEc → 0 < κ → (∀ (v : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))), sEEc v = Tw.mk (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (((1 : ℂ) * (κ : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) (sS.toRealSpectralMatching R).X (sS.toRealSpectralMatching R).G (Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c) ⟨x.R.HE.e (Tw.out v), hx⟩) ∧ RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2) → ∃ y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R), HEq y.tS q.saturationAtWeightedPoint.t ∧ y.cS = q.saturationAtWeightedPoint.c ∧ HEq y.Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core_data_of_point.row.kKs q.core_data_of_point.row.hk) ∧ HEq y.nexp.eF q.core_data_of_point.row.nexp.eF ∧ HEq y.nexp.fi q.core_data_of_point.row.nexp.fi ∧ y.uS = 1 := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 hL N Γ p hp hNE K q hHost hMult R hPin sP sS hsP hsS a x hax hin hsp κ sEEc hsEE hκ hdef
  obtain ⟨hsee, hev, -⟩ := GlobalTheory.Mem.R3.StageMove.spectralStage_point_rowPlacement_transfer K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a _ q.saturationAtWeightedPoint
  obtain ⟨Sx, nx, hSx, heF, hfi⟩ := _root_.GlobalTheory.Mem.R3.SelRealIn.exists_ratDat_nExpRealS q a x hax
  have hψ := _root_.GlobalTheory.Mem.R3.SelRealIn.psi_eq_theta_psi_of_recPin q R hPin x
  have eax : a.x = x := eq_of_heq hax
  rw [eax] at hsee hev
  obtain ⟨hH, -, -, hpos, -, -, hV, hX⟩ := hHost (q.w.st q.Z) q.x.isOver
  have hc : R.T.cols = q.x.col.C := hPin.s.cols
  have hF : (fun u => (R.T.cols.forms u).to0) = fun u => (q.x.col.C.forms u).to0 := by rw [hc]
  have e : (⟨_, sP⟩ : Σ F : ∀ u, Formalism.L2.Forms.Forms0 (q.w.D q.Z) u, GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) F) = ⟨_, q.saturationAtWeightedPoint.P⟩ :=
    Sigma.ext hF hsP
  have hm := (congrArg (fun z : (Σ F : ∀ u, Formalism.L2.Forms.Forms0 (q.w.D q.Z) u, GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) F) =>
      SeeAt x.R.toRealDat x.F.lv2 z.2.X z.2.inst q.saturationAtWeightedPoint.t ∧
      EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) z.2.X z.2.G
        (iotaX z.2.X z.2.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c) e).mpr ⟨hsee, hev⟩
  refine ⟨{ psiPin := hψ
            hin := hin
            spPin := (by with_unfolding_all exact (hsp :))
            Sx := Sx
            nexp := nx
            stdV := (by with_unfolding_all exact (hV :))
            stdX := (by with_unfolding_all exact (hX :))
            tS := q.saturationAtWeightedPoint.t
            cS := q.saturationAtWeightedPoint.c
            κS := κ
            ιS := (iotaX sP.X sP.inst).toMulEquiv
            instEq := (by with_unfolding_all exact (sP.inst :))
            ιS_eq := (by with_unfolding_all exact ((GlobalTheory.Mem.JIota.heq_iota_iff (q.w.D q.Z) sP.X sP.inst (iotaX sP.X sP.inst).toMulEquiv).2 rfl :))
            sEEc := sEEc
            sEEj := hsEE
            seeLev := fun _ => (by with_unfolding_all exact (hm.1.conj :))
            seeEval := fun _ => (by with_unfolding_all exact (hm.2 :))
            uS := 1
            uS_norm := norm_one
            seeDef := fun v hx => (by with_unfolding_all exact ((hdef v hx).1 :))
            seeK := ⟨hκ, fun _ v hx => (by with_unfolding_all exact ((hdef v hx).2 :))⟩
            host := (by with_unfolding_all exact (hH :))
            vpos := (by with_unfolding_all exact (hpos :)) }, HEq.rfl, rfl, hSx, heF, hfi, rfl⟩
end GlobalTheory.Mem.R3.SelRealIn
end
