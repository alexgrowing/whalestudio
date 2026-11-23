import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceUpperBoundAllMembers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
end GlobalTheory.LevelPrimeUpper
namespace GlobalTheory.LevelPrimeUpper
open Formalism.MainNotions.StandardLattice Finset
theorem levelPrime_le_at_points_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
      (fun κ D O _ _ => ∀ u : D.what₂.Word, Formalism.MainNotions.S.Tr D u ≤ O.L.sc.b ^ (κ.C.CTu * (D.R.m : ℝ))) := by
  intro hL p
  exact eventually_trace_le.mono fun _ _ _ H β _ _ _ _ => H β
end GlobalTheory.LevelPrimeUpper
end
