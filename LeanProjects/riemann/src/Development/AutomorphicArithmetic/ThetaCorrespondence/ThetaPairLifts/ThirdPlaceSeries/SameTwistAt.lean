import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameTwistAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.HeightCounting.SameTw
theorem sameTwist_at_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf C tp → GlobalTheory.HeightCounting.SameTw.OneField D C → GlobalTheory.PtCore.SameTwist D C :=
  fun _ D _ C _ a h => sameTwist_of_oneField D C a.all.nct h
end GlobalTheory.HeightCounting.SameTw
end
