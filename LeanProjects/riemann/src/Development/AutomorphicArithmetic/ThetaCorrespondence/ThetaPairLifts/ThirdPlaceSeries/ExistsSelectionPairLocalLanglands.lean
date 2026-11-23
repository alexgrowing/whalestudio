import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelectedRealization
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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServTIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRowsKCColPinsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
local macro:max "kq% " e:term:max : term => `((by kexactB $e))
noncomputable section
namespace GlobalTheory.Mem.R3.SelectionPairing
open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.IndefR.AutomorphicEvaluation
section Args
variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}
end Args
set_option maxHeartbeats 1000000 in
theorem wp3_ne_bot_and_piece_at_of_multEq (hWR : GlobalTheory.Published.WeilRepresentationUnitaryPair) (hDSE : GlobalTheory.Published.DiscreteSeriesExists)
    (hHCF : GlobalTheory.Published.HarishChandraFinite) (hCRD : GlobalTheory.Published.CuspRapidDecay) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
    (q : WPt p.s K) (hMult : GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) :
    ∀ p', q.x.what₂.r.z.R.EEp3 p' ≠ ⊥ → ∀ i, q.x.what₂.r.z.R.Wp3 i p' ≠ ⊥ ∧
      ∀ v, v ≠ (famT q.x.what₂).A.v0 → q.x.what₂.r.z.R.PartAt q.x.what₂.r.z.F i p' v :=
  GlobalTheory.T.rowPart_forms_and_nonzero_vectors_every_place _ _ _ _ _ _ _ q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.cG
    (GlobalTheory.LinksInputs.inputs_of_hypotheses hWR hDSE hHCF hCRD _) q.x.what₂.r.z.pins q.x.what₂.r.intersectionNumber_baseChange hMult
    (GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.pins.char 1 q.x.what₂.r.intersectionNumber_baseChange.ok
      (fun k => ⟨_, q.core_data_of_point.a.all.types.O k, q.core_data_of_point.a.all.types.eSer_def k⟩)).1
set_option maxHeartbeats 1000000 in
theorem ev_at_join_pinned {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex) (hR : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R)
    (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (hsP : HEq sP q.saturationAtWeightedPoint.P) :
    EvalTieT (Formalism.L2.SG.RowsJoinPinned.MP q.x.what₂.r.z.R.toRealDat) q.x.what₂.r.z.R.toRealDat.ν0
      q.x.what₂.r.z.R.toRealDat.fd0 (Formalism.L2.SG.RowsJoinPinned.EP q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2) sP.X sP.G
      (Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c := by
  have hF0 : (fun u => (R.T.cols.forms u).to0) = (fun u => (q.x.col.C.forms u).to0) := (by with_unfolding_all exact (congrArg (fun (C : type_of% q.x.col.C) u => (C.forms u).to0) hR.s.cols :))
  exact (by with_unfolding_all exact (pack_move (D := (q.w.st q.Z).toD7) (F0 := fun u => (R.T.cols.forms u).to0) (F0' := fun u => (q.x.col.C.forms u).to0)
    ((hF0)) (P := (sP)) (P' := (q.saturationAtWeightedPoint.P)) ((hsP))
    (fun _ P => EvalTieT (Formalism.L2.SG.RowsJoinPinned.MP q.x.what₂.r.z.R.toRealDat) q.x.what₂.r.z.R.toRealDat.ν0
      q.x.what₂.r.z.R.toRealDat.fd0 (Formalism.L2.SG.RowsJoinPinned.EP q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2) P.X P.G
      (Formalism.L2.SG.RowsJoinPinned.iotaX P.X P.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c) ((q.saturationAtWeightedPoint.ev)) : _))
theorem nonempty_rXs_of_prmR_none {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {Γ : GeoP} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} (hp : p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ) {K : Ctx}
    (q : WPt p.s K) : Nonempty (RXs q.x.what₂) := by
  subst hp
  exact (by with_unfolding_all exact (Nonempty.intro q.x.rx :))
end GlobalTheory.Mem.R3.SelectionPairing
end
open GlobalTheory.Mem.R3.SelectionPairing in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.R3.SelectionPairing.exists_selection_pair_local_langlands_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (Del h0 : ℕ) (c : ℝ) (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toRealSpectralMatching R).X u (sS.toRealSpectralMatching R).Y.hK), ∃ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x ∧ ∃ C : _root_.GlobalTheory.Cp.SquareIntegrableColumns R.T (divisionPairOfAdelicFormsFaceColumnsData x), HEq (fun Zs => C.c.face Zs) x.F.Dc ∧ HEq C.Sp x.F.Sp ∧ HEq C.c.W q.B.wts ∧ HEq C.c.Xg q.x.what₂.r.z.Xg ∧ _root_.Formalism.L2.DIV.ColumnCharactersCompatible C.toS ∧ x.F.Zsc = GlobalTheory.Fc.zsc (divisionPairOfAdelicFormsFaceColumnsData x) Del h0 c ∧ HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := (sS.toRealSpectralMatching R).X) (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) (sS.toRealSpectralMatching R).Y.hK (sS.toRealSpectralMatching R).G x.wd (fun m => _root_.Formalism.IndefR.pwOf_alt (sS.toRealSpectralMatching R) hin (x.wd m)) x.bR) ∧ ∃ (κ : ℝ) (sEEc : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX (sS.toRealSpectralMatching R).X)), HEq x.sEE sEEc ∧ 0 < κ ∧ ∀ (v : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))), sEEc v = Tw.mk (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (((1 : ℂ) * (κ : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) (sS.toRealSpectralMatching R).X (sS.toRealSpectralMatching R).G (Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c) ⟨x.R.HE.e (Tw.out v), hx⟩) ∧ RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2 := by
  intro hDS hHC hCW hWR hDSE hHCF hCRD hGAR hRay hL N Γ p hp hNEb K q hHost hMult R hR sP sS hsP hsS Del h0 c hin
  have hRX : Nonempty (RXs q.x.what₂) := _root_.GlobalTheory.Mem.R3.SelectionPairing.nonempty_rXs_of_prmR_none hp q
  have h := _root_.GlobalTheory.T.exists_square_integrable_columns_of_heq_data _ K q R.T.ker hR.k hRX
  refine h.elim fun Dc h => h.elim fun Sp₀ h => h.elim fun Zsc₀ h => h.elim fun C₀ hC => ?_
  have hcore := selection_group_ambient_tie (K := K) (w := q.w) (Z := q.Z) (Wt := q.x.Wt) (ex := q.O.ex) (t := q.x.what₂)
    ⟨hDS, hHC, hCW, hHCF, hCRD⟩ ((by with_unfolding_all exact (q.x.obj.amb :))) ((by with_unfolding_all exact (q.x.obj.mjH :))) ((by with_unfolding_all exact (q.core_data_of_point.row.grp :)))
    ((by with_unfolding_all exact ((_root_.GlobalTheory.Mem.R3.SelectionPairing.wp3_ne_bot_and_piece_at_of_multEq hWR hDSE hHCF hCRD q hMult) :))) Dc Sp₀ Zsc₀ ((by with_unfolding_all exact (C₀ :))) (sS.toRealSpectralMatching R).X ((by with_unfolding_all exact ((sS.toRealSpectralMatching R).Y.hK :)))
    ((by with_unfolding_all exact ((sS.toRealSpectralMatching R).G :))) ((by with_unfolding_all exact ((_root_.Formalism.IndefR.pwOf_alt (sS.toRealSpectralMatching R) hin) :)))
    ((by with_unfolding_all exact ((Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv :))) ((by with_unfolding_all exact (q.saturationAtWeightedPoint.t :))) q.saturationAtWeightedPoint.c q.saturationAtWeightedPoint.c_pos
    ((by with_unfolding_all exact ((_root_.GlobalTheory.Mem.R3.SelectionPairing.ev_at_join_pinned q R hR sP hsP) :))) q.O.L Del h0 c
  refine hcore.elim fun a h => h.elim fun x h => ?_
  have hc := hC R.T rfl a x h.1 ((by with_unfolding_all exact (h.2.1 :))) ((by with_unfolding_all exact (h.2.2.1 :))) ((by with_unfolding_all exact (h.2.2.2.1 :)))
  refine hc.elim fun C c' => ?_
  refine Exists.intro a (Exists.intro x (And.intro h.1 (Exists.intro C (And.intro c'.1 (And.intro c'.2.1 (And.intro c'.2.2.1
    (And.intro c'.2.2.2.1 (And.intro c'.2.2.2.2 (And.intro ?_ (And.intro ?_ ?_))))))))))
  · exact (by with_unfolding_all exact (h.2.2.2.2.1 :))
  · exact (by with_unfolding_all exact (h.2.2.2.2.2.1 :))
  · exact (by with_unfolding_all exact (h.2.2.2.2.2.2 :))
end
