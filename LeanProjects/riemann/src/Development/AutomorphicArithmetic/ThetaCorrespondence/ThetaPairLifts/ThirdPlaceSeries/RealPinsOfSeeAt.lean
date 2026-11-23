import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDataOfWitness
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelSideRT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServTIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPinsRealTOf
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.LinkedPins
set_option maxHeartbeats 4000000 in
theorem realPins_of_seeAt_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {K : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX} {x : TwIn ex} {Rc : _root_.Formalism.L2.RecTAlt ex}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) {P : SPack D fun u => (Rc.T.cols.forms u).to0} (sS : SRest P)
    (e : S = sS.toRealSpectralMatching Rc) (hC : x.R.C = Rc.T.n.cf) (hD : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i))
    (hPg : open Classical in x.R.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE))
    (hs : SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) := by
  subst e
  have hι : y.ιS = (iotaX P.X P.inst).toMulEquiv := (by with_unfolding_all exact ((GlobalTheory.Mem.JIota.heq_iota_iff D P.X P.inst ((y.ιS))).1 ((y.ιS_eq)) : _))
  refine _root_.GlobalTheory.Mem.R3.realPins_realTOf_alt _ _ _ _ _ _ _ _ ex x Rc _ y hC hD hPg hs.fin ?_ ?_
  · rw [hι]
    exact (by with_unfolding_all exact (hs.conj :))
  · exact (by with_unfolding_all exact (hs.mat :))
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
set_option maxHeartbeats 4000000 in
theorem realisation_normalisation_of_bundle_witness (q : WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) := by
  obtain ⟨x, a, ax, y, recPin, ⟨sP, sS, hP, -, e⟩, ⟨pt, -⟩, _⟩ := w
  cases ax
  obtain ⟨h1, h2, -⟩ := twArgs_lev _ _ _ _ _ _ _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have hk := recPin.k.std
  have fd : ∀ V : Formalism.BasicNotions.TH.HSp (q.w.D q.Z), GlobalTheory.Mem.HostFrames.SignFrame V → IsFDiag V := fun V hV => by
    obtain ⟨d, -, h⟩ := hV.gram_eq (q.w.D q.Z).host.F
    exact ⟨d, h⟩
  have hWV := (GlobalTheory.Mem.HostFrames.frames_of_over K (q.w.st q.Z) q.x.isOver).2.1
  refine _root_.GlobalTheory.Fam.LinkedPins.realPins_of_seeAt_alt y.y sS e ?_ (fun i => ⟨fd _ (hWV i).1, fd _ (hWV i).2⟩) ?_ ?_
  · have hc : b.R.T.n.cf = TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst recPin.s.chr
    have hC : Top.Fr.at (q.w.st q.Z) q.w.I.C = Top.Fr.at (q.w.st q.Z) q.f := congrArg (Top.Fr.at (q.w.st q.Z)) q.w.C_eq
    exact (eq_of_heq h1).trans (hC.symm.trans hc.symm)
  · rw [image_congr hk.X_eq hk.seam hk.Pr]
    exact (eq_of_heq h2).trans (image_refl _ rfl _).symm
  · have ht : y.y.tS = q.saturationAtWeightedPoint.t := eq_of_heq pt
    have hcols : b.R.T.cols = q.x.col.C := recPin.s.cols
    rw [ht]
    exact seeAt_twArgs a sP.X sP.inst q.saturationAtWeightedPoint.t (setting_congr (D := (q.w.st q.Z).toD7)
      (fun X h => SeeAt (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2 X h q.saturationAtWeightedPoint.t)
      (congrArg (fun C u => (C.forms u).to0) hcols) hP q.saturationAtWeightedPoint.see)
end GlobalTheory.Fam.LinkedPins
open GlobalTheory.MiS GlobalTheory.Fam in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Fam.realPins_bundle_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := by
  intro hL p K q c b w
  show (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisation k.B.Q) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)
  rw [w.y.eq]
  exact _root_.GlobalTheory.Fam.LinkedPins.realisation_normalisation_of_bundle_witness q b w
end
