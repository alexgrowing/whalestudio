import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaPrimeAllPoints
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
namespace GlobalTheory.LiftWeightForced
open Formalism.IndefR.IndefiniteWeightData
variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)
end GlobalTheory.LiftWeightForced
theorem GlobalTheory.LiftWeightForced.atPts_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) τ,
    Formalism.IndefR.Bridge.IsLamPrime (D := Fm.D x i)
      (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x _ i _ _ _ j τ => GlobalTheory.LiftWeightForced.isLamPrime_lamLdef (Fm.D x i) j τ⟩⟩
end
end
