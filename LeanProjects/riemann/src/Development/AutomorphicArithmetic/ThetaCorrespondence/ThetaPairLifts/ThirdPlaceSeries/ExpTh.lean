import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpTh
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
def ysTh_alt (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    NExpRealS (datTw x (thTw (Dof x) th)).R (datTw x (thTw (Dof x) th)).cG ((thTw (Dof x) th).rat l.rat.S) where
  fi := (by with_unfolding_all exact (l.b.YS.fi :))
  geq := (by with_unfolding_all exact (l.b.YS.geq :))
  rho := (by with_unfolding_all exact (l.b.YS.rho :))
  chi := (by with_unfolding_all exact (l.b.YS.chi :))
  eF := (by with_unfolding_all exact (l.b.YS.eF :))
  bsup := (by with_unfolding_all exact (l.b.YS.bsup :))
  act := kc% l.b.YS.act
def exponentOfTheta (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    NExpTied (w.st (oTw x (thTw (Dof x) th)).Z).toD7 :=
  (by with_unfolding_all exact ((bsTw l.b.Bs th).exp :))
def rowPsiOfTheta (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    ∀ i : Fin (w.st (oTw x (thTw (Dof x) th)).Z).toD7.R.m,
      Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (oTw x (thTw (Dof x) th)).Z).toD7 i)
        (w.st (oTw x (thTw (Dof x) th)).Z).toD7.R.nV :=
  fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV ((i)))) : _))
end GlobalTheory.HeightCounting.Up
end
end
