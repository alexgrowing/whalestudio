import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lb1OfRestagingBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.SerCarry
open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr
theorem st_facts_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (g : Geo x) (hg : GlobalTheory.RealGeo.InGeo g) (a : BigHost (Dof x)) :
    HkAd (sideAt x g hg a) l.rat.In.Sb ((l.rat.In.hL)) ∧ KeepsMat (D := Dof x) fun i => (l.mt.ad.PV i).ψ :=
  ⟨(l.rat.rat.hecke), x.r.Y.hF, l.mt.ad.id⟩
end GlobalTheory.HeightCounting.SerCarry
end
end
