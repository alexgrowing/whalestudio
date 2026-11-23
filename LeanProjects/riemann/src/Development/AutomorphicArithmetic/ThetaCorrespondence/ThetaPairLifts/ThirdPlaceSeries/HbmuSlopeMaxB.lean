import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.ValueBounds.SlopeMaxB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.L2.DIV.SlopeMaxB
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.DIV.Proofs Formalism.MainNotions.DIV.Proofs.HHParts
theorem colTies_of_sel_alt {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) : RT.tCVTies Fm := by
  obtain ⟨b, hs⟩ := stabF Fm
  refine ⟨max (max s.1 b) (Fm.x1 + 1), fun x hx i => ?_⟩
  have h1 : Fm.x1 < x := by have := le_trans (le_max_right _ _) hx; linarith
  have h0 : s.1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hb : b ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  exact ⟨⟨(s.2 x h1 h0 i).T.cols⟩, hs x hb h1 i⟩
theorem eventually_muMax_le_pow_ebMu_mul_of_tuSize {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) (hT : TuSize Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      (((Fm.D x i).fm u).lat 0).muMax ≤ (Fm.L x i).sc.x ^ EbMu Fm.cOut * (Fm.L x i).sc.b :=
  boundB_of_values Fm hT (tCV_of_ties Fm (_root_.Formalism.L2.DIV.SlopeMaxB.colTies_of_sel_alt s))
end Formalism.L2.DIV.SlopeMaxB
end
end
