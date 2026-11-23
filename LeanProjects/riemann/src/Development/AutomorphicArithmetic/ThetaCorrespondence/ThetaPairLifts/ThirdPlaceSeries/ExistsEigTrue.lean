import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigOfRatAd
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SCuspRows
set_option maxHeartbeats 1000000 in
theorem exists_eigTrue_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x) (n : InRat x.r.Y x.m.z.cG) :
    ∃ Sb, GlobalTheory.TwInputs.EigTrue (Dof x) (cfOf x) l.a.A.row Sb n.In.eig := by
  obtain ⟨Sb, h1, h2, -⟩ := GlobalTheory.TwInputs.Eig.exists_low (ι := Empty) n.In.Sb (fun i => i.elim) (fun i => i.elim) fun i => i.elim
  have h := _root_.GlobalTheory.TwInputs.Eig.eigTrue_of_read hL x.r.Y x.m.z.lev.is l.a.A.wdT l.a.A.row l.a.row n.rat.eig h1 h2
  have hC : x.m.z.R.C = cfOf x := x.m.z.lev.C
  exact ⟨Sb, (congrArg (fun c : CharFrame (Dof x) => GlobalTheory.TwInputs.EigTrue (Dof x) c l.a.A.row Sb n.In.eig) hC).mp h⟩
end GlobalTheory.SCuspRows
end
