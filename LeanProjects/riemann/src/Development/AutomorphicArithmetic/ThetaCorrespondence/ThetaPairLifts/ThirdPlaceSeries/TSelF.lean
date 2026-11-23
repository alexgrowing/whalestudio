import Formalism.LocalToGlobal.ThresholdSelection
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
def TwistSelectionFunctions {eps : ℝ} (Fm : FamP eps) : Type _ :=
  Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.RecTAlt (Fm.ex x hx i)
def TwistSelection (𝒞 : FamClass) : Type _ := ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → _root_.Formalism.L2.TwistSelectionFunctions Fm
theorem TwistSelectionFunctions.tiedRec {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) :
    ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.ExtraDataRecursive (Fm.ex x hx i) :=
  ⟨s.1, fun x hx h i => ⟨s.2 x hx h i⟩⟩
end Formalism.L2
end
end
