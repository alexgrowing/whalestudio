import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelSideRT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServTIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Pack
open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure RealPackage {D : D7} {O : Obj D} (R : _root_.Formalism.L2.RecTAlt O.ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) : Type 1 where
  P : RowSideFamily O.ex
  Dc : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Sp : ∀ Zs, SPer (Dc Zs)
  Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3
  B : _root_.Formalism.IndefR.RealTBAlt R P Dc Sp Zsc S
def realPackageOfBundle {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S :=
  ⟨b.P, b.C.c.face, b.C.Sp, GlobalTheory.Fc.zsc b.P b.DH.1.1 b.DH.1.2 c, b.B⟩
def realPackageOfRealInput {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {x : R3.TwIn O.ex} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R S) :
    _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S := ⟨R3.divisionPairOfAdelicFormsFaceColumnsData x, x.F.Dc, x.F.Sp, x.F.Zsc, _root_.GlobalTheory.Mem.R3.boundedRealisationOfInput y⟩
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure TwistedBundle {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) : Type 1 where
  intersectionNumber_baseChange : R3.Holds x.R x.F
  y : _root_.GlobalTheory.Mem.R3.RealInAlt x b.R b.S
  r : _root_.GlobalTheory.Mem.R3.RecursiveInput y
  eq : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y
  HD : _root_.Formalism.L2.HostDatumWithTies b.R.T.toTiedDataS
end Pack
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
def WPt.saturationAtWeightedPoint (q : WPt p.s K) :
    SAt (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R.toRealDat q.x.what₂.r.z.F.lv2 q.x.what₂.r.Y.eE fun u => (q.x.col.C.forms u).to0 := q.x.sx.1
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure BundleWitness (q : WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) : Type 1 where
  x : R3.TwIn q.O.ex
  a : R3.TwArgs q.O.ex q.x.what₂
  ax : HEq a.x x
  y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x
  recPin : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q b.R
  s : ∃ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (b.R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP),
    HEq sP q.saturationAtWeightedPoint.P ∧ HEq sS q.saturationAtWeightedPoint.S ∧ b.S = sS.toRealSpectralMatching b.R
  pt : HEq y.y.tS q.saturationAtWeightedPoint.t ∧ y.y.cS = q.saturationAtWeightedPoint.c
  sx : HEq y.y.Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core_data_of_point.row.kKs q.core_data_of_point.row.hk)
  eF : HEq y.y.nexp.eF q.core_data_of_point.row.nexp.eF
  fi : HEq y.y.nexp.fi q.core_data_of_point.row.nexp.fi
  uS : y.y.uS = 1
  parts : (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput y.r).PartsRow
  cW : HEq b.C.c.W q.B.wts ∧ HEq b.C.c.Xg q.x.what₂.r.z.Xg
  d3b : HEq y.HD.d3b q.x.pin.d3b
  side : _root_.Formalism.L2.SelectedSideOfRealRecord b.R (R3.divisionPairOfAdelicFormsFaceColumnsData x) (_root_.GlobalTheory.Mem.R3.realisationOfInput y.y) (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput y.r) y.HD q.core_data_of_point.a.Pq
  colPins : _root_.Formalism.L2.DIV.ColumnCharactersCompatible b.C.toS
def BundleLinkage (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : GlobalTheory.Fc.LkT _root_.GlobalTheory.Fc.BundleCondition :=
  linkOf (𝒮 := p.s) (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ q _ b => Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := p) q b)
end GlobalTheory.Mem.Top.Bl
end
end
