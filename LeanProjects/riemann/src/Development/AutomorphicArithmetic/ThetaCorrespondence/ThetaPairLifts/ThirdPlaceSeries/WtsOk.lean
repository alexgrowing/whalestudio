import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLambdaShiftNonneg
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsImp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParOfFurtherStatement

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie.Lift
open Formalism.IndefR.Bridge
theorem wts_ok_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ W : Formalism.CohomologicalDescent.ShortWeightBounds.Wts (Fm.D x i).what₂.Tau, W.Ok (GlobalTheory.ExpTie.parOf (Fm.L x i) j) ∧
    (∀ τ, ∃ c : ℤ, ∀ a : Fin (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank,
      (W.lam τ a : ℤ) = (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ).w a + c) ∧
    (∀ τ a, a < (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Nr → 0 ≤ W.U (GlobalTheory.ExpTie.parOf (Fm.L x i) j) τ a ∧ W.U (GlobalTheory.ExpTie.parOf (Fm.L x i) j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf (Fm.L x i) j) : ℤ)) ∧
    W.T2.card ≤ (Fm.D x i).host.T2.card ∧ W.Sp = Formalism.MainNotions.JumpSetsAlt.excSet (Fm.D x i) := by
  refine _root_.GlobalTheory.ExpTie.atPts_mono (_root_.GlobalTheory.ExpTie.atPts_and_alt _root_.GlobalTheory.T.isLamPrime_at_all_points _root_.GlobalTheory.T.parameter_large_at_all_points) ?_
  intro eps Fm x hx i p hp j
  obtain ⟨hF, hLg⟩ := hp
  have hv : ∀ τ, ValsAt (Fm.L x i) j τ := fun τ => GlobalTheory.T.liftWeightRho_entryValues (Fm.L x i) j τ (hF j τ)
  refine ⟨wts (Fm.L x i) j, ⟨anti _ j, what₂ _ j, fun τ => (GlobalTheory.T.liftWeightRho_block_constant_centred (Fm.L x i) j τ (hv τ)).1, fun τ => (GlobalTheory.T.liftWeightRho_block_constant_centred (Fm.L x i) j τ (hv τ)).2,
    fun τ => (GlobalTheory.T.liftWeightRho_window_contains_cloud (Fm.L x i) j τ (hv τ)).1, fun τ => (GlobalTheory.T.liftWeightRho_window_contains_cloud (Fm.L x i) j τ (hv τ)).2,
    fun τ => GlobalTheory.T.liftWeightRho_lows_distance_bounds (Fm.L x i) (Fm.params x hx i) j τ (hv τ), fun τ h => GlobalTheory.T.liftWeightRho_thickPlace_centre_window (Fm.L x i) j τ (hv τ) h,
    fun τ h => GlobalTheory.T.liftWeightRho_nonThickPlace_centre_width (Fm.L x i) (Fm.params x hx i) j τ (hv τ) h⟩, fun τ => ⟨-(lamL j τ).detShift, fun a => ?_⟩,
    fun τ a ha => ⟨U_nonneg _ j τ a ha, GlobalTheory.T.liftWeightRho_entries_le_floor_height (Fm.L x i) (Fm.params x hx i) j τ (hLg j) (hv τ) a ha⟩, T2_card _ j, rfl⟩
  have := lamT_of_lt j τ a a.2
  show (lamT j τ a : ℤ) = _
  rw [this]
  ring
end GlobalTheory.ExpTie.Lift
end
end
