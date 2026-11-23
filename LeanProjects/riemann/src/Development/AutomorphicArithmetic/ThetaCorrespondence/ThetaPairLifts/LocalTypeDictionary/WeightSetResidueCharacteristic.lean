import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsFromPrintedInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RationalDataSizedFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsFromPrintedInputsStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
noncomputable section
namespace GlobalTheory.Mem.R3.Rw.AtDatumEvaluation
open GlobalTheory.Mem.Top.GroupRetwisting
set_option maxHeartbeats 2000000 in
theorem atDat_holds_alt (hP : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems) (hL : GlobalTheory.Published.HeckeLPartialContinuation) :
    AtDat fun _ _ _ _ _ _ _ _ z => GlobalTheory.CuspMult.MultEq z.R.toRealDat → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) →
      GlobalTheory.Mem.R3.Holds z.R z.F := by
  have e1 := (evG_of_ev (ev_scale (_root_.GlobalTheory.T.rational_data_sized_family_alt hP hL))).inter
    ((evG_of_ev LedRec.ev_exists_sizeData).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev))
  have s1 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (evLgG_of_evLg GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField)
  have s2 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (q := fun _ => CoverAt.WeberLev) (evG_all CoverAt.lg_weberLev)
  refine (s1.and (s2.and (Step.and (lUnif_atDat hP.q3 hP.q2 hP.q1) (atDat_lIntegral hP.q3 hP.q2 hP.q1)))).trans
    (Step.of_evG (e1.imp ?_))
  rintro K - - - - ⟨⟨x₀, hx, hH⟩, hLed, hHost⟩ B f T hO - - ⟨hOk, hW, hU, hI⟩ w hw Z hX Wt z g1 g2 hEx g4 hM hR
  obtain ⟨Z', g1', hη, hA⟩ := LedRec.exists_bare hP.q12 (B := B) (C := w.C) Z f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨L, hsc, hsz, hpar, hn⟩ := hLed (w.st Z') hO hη hA
  obtain ⟨hhost, -, -, -, -, -, hV, -⟩ := hHost (w.st Z') hO
  have s : SameGrp Z Z' := LedRec.sameGrp g1 g1'
  refine DatCopy.holds_of_copy Z' s ?_
  have hEx' := DatCopy.copy_exAt Z' s hEx
  have hU' := DatCopy.copy_lUnif Z' s (hU w hw Z hX Wt z g1 g2 hEx g4)
  have hI' := DatCopy.copy_lIntegral Z' s (hI w hw Z hX Wt z g1 g2 hEx g4)
  have hM' := DatCopy.copy_multEq Z' s hM
  have hR' := DatCopy.copy_rowTest Z' s hR
  generalize DatCopy.copy Z' s z = y at hEx' hU' hI' hM' hR' ⊢
  have hch := y.pins.char
  have hT : TypesTrue (w.st Z').toD7.ntypes y.R.C.P y.R.C.W := by
    rw [y.lev.C, w.C_eq]
    exact g1'
  have hIo : IoExt y.R.toRealDat := GlobalTheory.T.ioExt_of_weakCharacterisation_of_orthonormal_frames _ _ _ _ _ _ _ y.R y.F hch hEx' hV
  have hOM : ∀ i, OneMapRowR y.core y.R.toRealDat y.geo.κ y.geo.v₀ y.geo.O (fun _ => 1) i := fun i =>
    GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation _ _ _ _ _ _ y.core y.R y.F y.geo.κ y.geo.v₀ y.geo.O (fun _ => 1) hn hch hEx' ⟨y.geo.fw⟩ hIo i
      (y.geo.pins i) (y.geo.phase i hU')
  exact hH (w.st Z') w.px w.I hX T Wt y L (by rw [hsc]) (by rw [hsc]; exact hx) hsz hpar
    ⟨(hOk w.px w.I hX w.ok w.C_eq w.xi_range).2 _ y.Xg y.tr y.good.irr, hch, hEx', hhost, ⟨L, hpar⟩, B.ccK_top, y.pins.keep.guard,
      GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hch.base.lev hT, serClause_of_typesTrue hP.q12 _ hT,
      GlobalTheory.Hk3.inertJunk_colIn3 _ _ _ hX _ _ _ _ _ _, y.pins.trSem, y.pins.keep.std, y.pins.phs, hn⟩
    (TiesG.of_dat y hU' hIo hOM (CoverAt.coverField_of_weberLev hW w Z' hX Wt y)) hM' hR' hI'
theorem w_of_multEq_and_test_at_weights : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → (StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) → GlobalTheory.CuspMult.MultEq z.R.toRealDat ∧ Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) → WeightCaseCondition := fun hP hL H =>
  (StepW.and H ((StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans (_root_.GlobalTheory.Mem.R3.Rw.AtDatumEvaluation.atDat_holds_alt hP hL))).trans
    (StepW.of_all fun _ _ _ _ _ _ _ G Z hX Wt z a b k c d e g u v =>
      G.2 Z hX Wt z a b c d (G.1 Z hX Wt z a b k c d e g u v).1 (G.1 Z hX Wt z a b k c d e g u v).2)
end GlobalTheory.Mem.R3.Rw.AtDatumEvaluation
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.w_of_weight_residue_char : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → (StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) → GlobalTheory.CuspMult.MultEq z.R.toRealDat ∧ Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) → WeightCaseCondition := by
  first | exact @_root_.GlobalTheory.Mem.R3.Rw.AtDatumEvaluation.w_of_multEq_and_test_at_weights | exact _root_.GlobalTheory.Mem.R3.Rw.AtDatumEvaluation.w_of_multEq_and_test_at_weights | (intros; apply _root_.GlobalTheory.Mem.R3.Rw.AtDatumEvaluation.w_of_multEq_and_test_at_weights <;> assumption)
end
