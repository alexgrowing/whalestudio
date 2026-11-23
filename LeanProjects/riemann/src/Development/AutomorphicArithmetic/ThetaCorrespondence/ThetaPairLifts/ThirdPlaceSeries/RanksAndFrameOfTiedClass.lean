import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RanksFramesClosed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExactRanksAlongTiedFamily

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory
theorem ranks_and_frame_of_tied_class_alt : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 →
    (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧
      Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  intro hU 𝒞 sel
  have hR : Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu :=
    Formalism.MainNotions.Pk.Closed.of_class fun Fm _ hc =>
      _root_.GlobalTheory.exact_ranks_along_tied_family_alt hU _ Fm (sel Fm hc) _ _ _ _ _ _
  exact ⟨hR, GlobalTheory.tFrame_of_ranksRow_three 𝒞 hR⟩
end GlobalTheory
end
