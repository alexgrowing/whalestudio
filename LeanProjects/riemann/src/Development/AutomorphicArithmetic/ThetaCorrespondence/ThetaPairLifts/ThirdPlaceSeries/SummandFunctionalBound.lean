import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRecPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NXNMjT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure PointSummands (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : _root_.Formalism.L2.RecTAlt O.ex
  S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R
  P : RowSideFamily O.ex
  pin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)
  ok1 : P.A3.fam3.Ok3 1
  B : _root_.Formalism.IndefR.RealTBAlt R P Dcf Spf (GlobalTheory.Fc.zsc P DH.1.1 DH.1.2 c) S
  Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q
  psi : PsiPPTie D P.P0 P.ψ0 P.Ps P.ψs P.I.eG
  pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q
  muDef : ∀ C CH : ℝ, (B.Q.Rl.toCx3 B.Q.F).MuDef B.Q.F.cr (B.Q.Rl.num B.Q.F C CH) B.Q.Rl.mu
  recPins : _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins Rr
def FiringPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b =>
  b.B.Q.Rl.toRealDat.ExAt ∧ JEvBar b.B.T b.B.Q.Rl.toRealDat b.B.κ ∧ GeoAct b.B.T b.B.Q.Rl.toRealDat b.B.κ b.B.v₀ ∧
    EvInj b.B.T b.B.Q.Rl.toRealDat b.B.v₀
def summandRealBound : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows b.B
def ThresholdPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b =>
  RecTie.ThetaFireRow (RecTie.toLiftReal b.B.Q.Rl.toRealDat b.B.Q.F.lv2 b.Rr.tupT b.Rr.hm b.Rr.hTop b.Rr.hinj) b.Rr.IL
def FramePointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx b.B.Q
def VisibleExamplePointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => _root_.Formalism.IndefR.IndefiniteRealisationExtends b.B.Q
def summandPrimitive : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3
def DivisorPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun D O _ b =>
  DivRows3 D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.Zs b.P.S0 b.P.S1 O.ex.p0 b.P.C b.P.NuC b.P.I
def summandDegreeZero : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun D _ _ b =>
  D.what₂.D0 = (b.P.A3.A.fam.R b.P.A3.A.fam.μ0).dZ (b.P.A3.A.fam.lvl b.P.P0 b.P.ψ0) (b.P.Zs.Z b.P.A3.A.fam.μ0)
def NormJumpPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ O _ b => _root_.Formalism.IndefR.NX.RealExpansionMajorant b.B.Q b.B.Q.cG b.B.Q.Sx b.B.Q.nexp O.ex.nch
def IotaPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ∀ x : b.S.X.B.I.E, HEq (b.S.X.ιE x) x
def summandL3Bound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).L3 (b.B.Q.Rl.num b.B.Q.F C CH)
def summandNormBound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).ON (b.B.Q.Rl.num b.B.Q.F C CH)
def summandL6Bound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr true).L6 (b.B.Q.Rl.num b.B.Q.F C CH)
def summandFunctionalBound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).FUN (b.B.Q.Rl.num b.B.Q.F C CH)
def SmallPointSummands (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b =>
  (∀ w, (b.B.Q.Rl.toCx3 b.B.Q.F).W1 b.B.Q.F.cr (b.B.Q.Rl.num b.B.Q.F C CH) w → w ∈ b.B.Q.Rl.twPl) ∧
    (b.B.Q.Rl.toCx3 b.B.Q.F).SEEIso b.B.Q.sEE ∧ PassIn3 b.B.Q.Rl b.B.Q.F C CH
end GlobalTheory.Fc.Ind
end
end
