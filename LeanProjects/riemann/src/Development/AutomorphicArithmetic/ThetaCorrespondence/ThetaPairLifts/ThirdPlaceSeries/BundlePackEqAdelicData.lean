import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfRepresentationTheoryOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberSizesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FramesExOfRealisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealAtColsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeeExJoinPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinSubspaceRealDataLatticeStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.PtRowsAt
section General
open NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
section Args
open GlobalTheory.Mem.Top.Bl
variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}
end Args
set_option maxHeartbeats 1000000 in
theorem see_join_alt (h5 : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX} (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex)
    (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (S0 : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (hS : S0 = S.toRealSpectralMatching Rc)
    (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S0) (c : ℝ) (hH : Holds x.R x.F) (hP : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y))
    (h : Placed x.R.toRealDat x.F.lv2 x.Y.eE P S y.tS c) :
    _root_.Formalism.IndefR.IndefiniteRealisationExtends (_root_.GlobalTheory.Mem.R3.realisationOfInput y) ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin Rc S0 (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) := by
  subst hS
  have hSch : SchurAll D := fun V _ S θ M J χ μ 𝓕 =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult h5.2.2.2.1 h5.2.2.2.2 D θ V S M J χ μ 𝓕).2
  have hL := (GlobalTheory.T.rowLattices_metrics_agree_of_realGroupTheorems h5 D _ _ _ _ x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.pins hH).1
  exact ⟨(_root_.GlobalTheory.Mem.JPin.seeEx_joinPin_alt _ _ _ _ _ _ _ _ _ x Rc P S y c hH h.1 h.2.1 h.2.2).1,
    (_root_.GlobalTheory.T.join_subspace_real_data_exists_alt _ _ _ _ _ _ _ _ _ x Rc P S y c 1 hSch hP hH hH.ok hH.sep hL
      (rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ x).2.1 h.1 h.2.1 h.2.2).1⟩
end General
section Wit
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} {q : Bl.WPt p.s K} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c}
theorem bundle_P_eq_divisionPair_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : b.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg _root_.GlobalTheory.Mem.Top.Bl.RealPackage.P w.y.eq
theorem dcPtG_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : DcPtG b.P := by
  rw [_root_.GlobalTheory.Fam.PtRowsAt.bundle_P_eq_divisionPair_of_bWit w]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).2.2.1
theorem realPins_of_bWit' (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := (_root_.GlobalTheory.T.characters_match_bundle_alt q b w).2.2.2.2.2.1
theorem framesEx_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx b.B.Q := by
  letI := b.B.alg
  exact _root_.GlobalTheory.FramesAtReal.framesEx_of_realisation_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b.B.Q (_root_.GlobalTheory.Fam.PtRowsAt.realPins_of_bWit' w)
theorem prim_links_and_typesSep3_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3 := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => Formalism.IndefR.Links.PrimRows3 r.B.Q.Rl r.B.Q.F ∧ r.P.A3.fam3.TypesSep3) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) :=
    ⟨w.y.intersectionNumber_baseChange.prim, w.y.intersectionNumber_baseChange.sep⟩
  rw [← w.y.eq] at h
  exact h
theorem exAt_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : b.B.Q.Rl.toRealDat.ExAt := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => r.B.Q.Rl.toRealDat.ExAt) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) := exAt_of_args w.a w.x w.ax
  rw [← w.y.eq] at h
  exact h
set_option maxHeartbeats 1000000 in
theorem seeEx_and_joinSI_nonempty_of_bWit (h5 : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    _root_.Formalism.IndefR.IndefiniteRealisationExtends b.B.Q ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin b.R b.S b.B.Q) := by
  obtain ⟨sP, sS, hP, hS, e⟩ := w.s
  have hpin : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisation r.B.Q) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := _root_.GlobalTheory.Fam.PtRowsAt.realPins_of_bWit' w
  rw [w.y.eq] at hpin
  have h0 := placed_of_args w.a w.x w.ax q.saturationAtWeightedPoint.P q.saturationAtWeightedPoint.S q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c ⟨q.saturationAtWeightedPoint.see, q.saturationAtWeightedPoint.ev, q.saturationAtWeightedPoint.rowJ⟩
  have ht : w.y.y.tS = q.saturationAtWeightedPoint.t := eq_of_heq w.pt.1
  have hF : (fun u => (b.R.T.cols.forms u).to0) = fun u => (q.x.col.C.forms u).to0 :=
    congrArg (fun C : type_of% q.x.col.C => fun u => (C.forms u).to0) w.recPin.s.cols
  have h1 := Placed.of_heq hF hP hS h0
  rw [← ht] at h1
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationExtends r.B.Q ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin b.R b.S r.B.Q)) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) :=
    _root_.GlobalTheory.Fam.PtRowsAt.see_join_alt h5 w.x b.R sP sS b.S e w.y.y q.saturationAtWeightedPoint.c w.y.intersectionNumber_baseChange hpin h1
  rw [← w.y.eq] at h
  exact h
end Wit
theorem good_linked_ptR_of_cuspRapidDecay : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) := by
  intro h1 h2 h3 h4 h5 hL p
  obtain ⟨Cl₀, hnc⟩ := GlobalTheory.Core.Rk.HdNc.hd_nc
  refine (_root_.GlobalTheory.T.exists_constants_for_parameters_scale_bundle hL p (fun _ _ => 0) (fun _ _ => max 1801 Cl₀) (fun _ _ => 0)).imp ?_
  rintro κ K β c b - - ⟨q, b', ⟨w⟩, he⟩ ⟨C', Cl, Cg, CT, -, hCl, -, hHD, -, -, hB, hrS⟩
  have key : ∀ s t : (Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c), s = t →
      (Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin t.2.2.R t.2.2.S t.2.2.B.Q) ∧ DcPtG t.2.2.P ∧ _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx t.2.2.B.Q ∧
        _root_.Formalism.IndefR.IndefiniteRealisationExtends t.2.2.B.Q ∧ t.2.2.B.Q.Rl.toRealDat.ExAt ∧
        (Formalism.IndefR.Links.PrimRows3 t.2.2.B.Q.Rl t.2.2.B.Q.F ∧ t.2.2.P.A3.fam3.TypesSep3)) →
      (Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin s.2.2.R s.2.2.S s.2.2.B.Q) ∧ DcPtG s.2.2.P ∧ _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx s.2.2.B.Q ∧
        _root_.Formalism.IndefR.IndefiniteRealisationExtends s.2.2.B.Q ∧ s.2.2.B.Q.Rl.toRealDat.ExAt ∧
        (Formalism.IndefR.Links.PrimRows3 s.2.2.B.Q.Rl s.2.2.B.Q.F ∧ s.2.2.P.A3.fam3.TypesSep3)) := by
    rintro _ _ rfl h
    exact h
  have hsj := _root_.GlobalTheory.Fam.PtRowsAt.seeEx_and_joinSI_nonempty_of_bWit ⟨h1, h2, h3, h4, h5⟩ w
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := key ⟨β.D, β.O, b⟩ ⟨q.w.D q.Z, q.O, b'⟩ he
    ⟨hsj.2, _root_.GlobalTheory.Fam.PtRowsAt.dcPtG_of_bWit w, _root_.GlobalTheory.Fam.PtRowsAt.framesEx_of_bWit w, hsj.1, _root_.GlobalTheory.Fam.PtRowsAt.exAt_of_bWit w, _root_.GlobalTheory.Fam.PtRowsAt.prim_links_and_typesSep3_of_bWit w⟩
  exact ⟨a1, a2, a3, a4, a5, a6,
    GlobalTheory.Core.Rk.finX_of_gap _ b.S.toSTies (gapHyp_of_hd ((le_max_left _ _).trans hCl) hHD),
    hnc _ _ _ _ _ _ _ _ _ ((le_max_right _ _).trans hCl) hHD b.S.X,
    GlobalTheory.Core.Rk.GapOfNodes.harishChandraNodesFarApart_of_cubic_node_gap _ hB, hrS⟩
end GlobalTheory.Fam.PtRowsAt
end
end
