import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.HeightCounting.Up.LiTw
section Gen
variable {D : D7} (N : TwNew D)
def sideA_alt {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding N.toD7 (N.cf cf) jE :=
  { bare := A.bare
    wdT := A.wdT
    lab := A.lab
    chr := { A.chr with }
    row := N.row A.row
    pl := { A.pl with }
    iota := A.iota
    wd := { A.wd with }
    grp := { A.grp with }
    par := { A.par with }
    au := { A.au with }
    chiT := A.chiT }
end Gen
end GlobalTheory.HeightCounting.Up.LiTw
end
end
