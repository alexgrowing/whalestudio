import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowEListPinPt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.LiteralAutomorphy.PinPt
open Formalism.L2.Host Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
theorem listPin_rpk_alt {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {x : GlobalTheory.Mem.R3.TwIn O.ex}
    (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R S) (r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S) (hr : r = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) {CF bb : ℝ}
    (h : GlobalTheory.HeightCounting.Up.ListPin D x.R.toRealDat.toLevCh CF bb) : GlobalTheory.HeightCounting.Up.ListPin D r.B.Q.Rl.toRealDat.toLevCh CF bb := by
  subst hr
  exact h
end GlobalTheory.Mem.LiteralAutomorphy.PinPt
end
