import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilUnitaryEntries
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServTIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVRecBridgeSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsUOfColPinsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtKOfReal
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.RL.DefSide
def PointEvaluationSide : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  (Formalism.L2.Theta.RealTied D ∧ ∃ C : Formalism.L2.Forms.ColsTiedSym D, ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u)) ∧
  _root_.Formalism.L2.DIV.ColumnCharactersCompatible b.C.toS ∧ ∃ W : Formalism.L2.Col.Wts b.R.T.ker.X b.R.T.ker.Pr.Word D.R, HEq b.C.toS.c.W W ∧
    GlobalTheory.ColRows.KerTies b.R.T.ker W b.DH.1.1 b.DH.1.2 ∧
    ∀ CY CT : ℝ, GlobalTheory.CoreHt.HtRowsS O.L CY → 8 ≤ O.L.sc.X' → 2 ≤ O.L.sc.x → (∀ u, 4 * O.L.sc.a < ((D.mem u).A.T : ℝ)) →
      (∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * O.L.sc.L) →
      GlobalTheory.ColRows.KerSizes b.R.T.ker W b.DH.1.1 b.DH.1.2 CY CT
theorem pointEvaluationSide_of_bWit {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide _ _ c b := by
  have hk := b.C.kerTie
  have e : Formalism.L2.Col.Wts _ b.C.c.Pr.Word b.C.c.Rk = Formalism.L2.Col.Wts b.R.T.ker.X b.R.T.ker.Pr.Word (q.w.D q.Z).R :=
    wts_eq hk.1.symm hk.2.2.1 hk.2.1
  have hW : HEq (cast e b.C.c.W) q.B.wts := (cast_heq e _).trans w.cW.1
  refine ⟨⟨q.x.real, GlobalTheory.T.exists_symmetricColumnForms_stepZeroFiniteCharacter q.w.I q.w.ok q.w.pins q.w.l q.Z⟩, w.colPins, cast e b.C.c.W, (cast_heq e _).symm, ?_, ?_⟩
  · exact GlobalTheory.T.kernelCompatibilities_standardKernelData_trueColumns q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex b.R.T.ker _ _ _ q.x.pin.jets w.recPin.k.std hW
      b.DH.2.1 b.DH.2.2 (b.R.T.ker_sharp _)
  · exact GlobalTheory.ColRows.kerSizes_of_stdKer q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex b.R.T.ker _ _ _ w.recPin.k.std hW
      b.DH.2.1 b.DH.2.2
theorem pointEvaluationSide_of_isLinked {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c)
    (h : _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p K β c b) : _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide _ _ c b := by
  obtain ⟨q, b', ⟨w⟩, e⟩ := h
  exact Eq.mpr (congrArg (fun y : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide y.1 y.2.1 c y.2.2) e) (_root_.GlobalTheory.Fc.RL.DefSide.pointEvaluationSide_of_bWit q b' w)
theorem definiteSideCondition_of_nprimeDef_of_nuFull (CY CT : ℝ) (hCT : 0 ≤ CT) : ∃ C0 : ℝ, ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (C CH : ℝ),
    _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide D O c b → GlobalTheory.CoreHt.HtRowsS O.L CY → 8 ≤ O.L.sc.X' → 2 ≤ O.L.sc.x → (∀ u, 4 * O.L.sc.a < ((D.mem u).A.T : ℝ)) →
      (∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * O.L.sc.L) → DV.NprimeDef D O.L → D.NuFull →
      (∀ u, 0 < (D.div.Nu u).rank) → C0 ≤ c → _root_.GlobalTheory.Fc.DefiniteSideCondition D O c b C CH := by
  obtain ⟨C0, hC0⟩ := _root_.GlobalTheory.T.kernel_columns_from_ties_alt CY CT hCT
  refine ⟨C0, fun D O c b C CH hE h1 h2 h3 h4 h5 hN hF hR hc => ?_⟩
  obtain ⟨-, hpin, W, hW, hT, hS⟩ := hE
  intro hok1 hsep hP hI lam0 c0 ce Sw C1 H NuC I _ hII u
  have hZs : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs = b.P.Zs := (_root_.GlobalTheory.Fc.qRealOfBundle b).zs
  have hS0 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.base.toIndefData b.P.S0 := (_root_.GlobalTheory.Fc.qRealOfBundle b).s0
  have hS1 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.toIndefData b.P.S1 := (_root_.GlobalTheory.Fc.qRealOfBundle b).s1
  have hDc : HEq (b.C.toS.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs) b.P.Dc :=
    (congr_arg_heq b.C.toS.c.face hZs).trans (heq_of_eq b.C.toS.colTie.1)
  have hw : HEq (I.wU u) u := ((Formalism.L2.DIV.divTieDat3_heq hZs hS0 hS1 hDc hII).2.2 u).trans (b.C.wTie u)
  exact hC0 D O.L _ _ _ _ _ _ O.ex b.R.T b.P b.C.toS W _ _ hpin hW hT (hS CY CT h1 h2 h3 h4 h5) hN hF hR _ _ C CH
    (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI) hZs u lam0 c0 ce c Sw C1 (H u) (I.wU u) (I.eNu u) hw hc
theorem linkedAt_df_of_parameters {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowDefectCondition := by
  refine _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (p := p) (H := Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ => True) fun C CH D O c b => _root_.GlobalTheory.Fc.DefiniteSideCondition D O c b C CH)
    ⟨fun _ => _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide, RowE.of_all fun _ _ β c b _ _ h => _root_.GlobalTheory.Fc.RL.DefSide.pointEvaluationSide_of_isLinked β c b h, fun 𝒜 σ s => ?_⟩
  choose c0 hc0 using fun (CY CT : ℝ) => _root_.GlobalTheory.Fc.RL.DefSide.definiteSideCondition_of_nprimeDef_of_nuFull CY (max CT 0) (le_max_right _ _)
  refine (Formalism.MainNotions.DIV.closed_Csz_ge_fn (W3 𝒜) fun l => c0 (l.getD 6 0) (l.getD 13 0)).imp ?_
  intro eps Fm CH _ hC hc _
  have hC' : c0 Fm.CYL Fm.CTu ≤ Fm.Csz := hC
  obtain ⟨κ, -, -, hs⟩ := s Fm (w3_a hc)
  have tie : RealPlaceSecondLayerConditions Fm := ⟨Fm.x1 + 1, fun x hx i => (hs x (by linarith) i).2.1⟩
  obtain ⟨CH', hCh⟩ := hc.2.1
  obtain ⟨⟨a1, hF⟩, ⟨a2, hR⟩⟩ := full_rank Fm CH' tie hc.2.2.1 hCh
  obtain ⟨a3, hz⟩ := GlobalTheory.CoreHt.famRowsSizes Fm hc.2.2.1
  refine ⟨0, le_rfl, fun C _ => ⟨max a1 (max a2 a3), fun x hx h0 i => ?_⟩⟩
  have e1 : a1 ≤ x := le_trans (le_max_left _ _) h0
  have e2 : a2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h0
  have e3 : a3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h0
  obtain ⟨z1, z2, z3, z4, z5⟩ := hz x e3 i ⟨_, (σ Fm (w3_a hc) x hx i).DH.2.1⟩
  exact hc0 Fm.CYL Fm.CTu _ _ _ (σ Fm (w3_a hc) x hx i) C CH (hs x hx i).2 z1 z2 z3 z4 z5 (Fm.nprimeDef x hx i)
    (hF x e1 i) (hR x e2 i) hC'
end GlobalTheory.Fc.RL.DefSide
theorem GlobalTheory.Fc.RL.linkedAt_prmR_df_of_cuspRapidDecay : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowDefectCondition :=
  fun _ _ _ _ _ N S Γ => _root_.GlobalTheory.Fc.RL.DefSide.linkedAt_df_of_parameters (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)
end
end
