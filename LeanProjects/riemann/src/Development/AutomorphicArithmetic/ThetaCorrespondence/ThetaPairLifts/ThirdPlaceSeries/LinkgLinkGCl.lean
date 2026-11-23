import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.AdmissibleClasses.LinkGCl
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GTiedFOfC2S
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.L2.DIV.LinkGCl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2.Top3
variable {eps : ℝ}
theorem gTiedF_of_sel_alt (Fm : FamP eps) (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) : Formalism.L2.G.GroupCompatibilityFamily Fm :=
  _root_.Formalism.L2.gTiedF_of_C2S_alt Fm (_root_.Formalism.L2.Top3.tied_families_of_choice_alt s)
theorem closed_linkG (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) : Closed (D3 3 𝒜) fun Fm _ => LinkG Fm :=
  Formalism.L2.G.linkG_concrete5 (D3 3 𝒜)
    (Closed.of_class fun Fm _ hc => _root_.Formalism.L2.DIV.LinkGCl.gTiedF_of_sel_alt Fm (sel Fm (d3_a hc)))
    (Closed.of_class fun Fm _ hc => admissible_tops_of_class Fm hc)
theorem closed_linkG_of_tuSize_dGamSize (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :
    Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm → LinkG Fm :=
  (_root_.Formalism.L2.DIV.LinkGCl.closed_linkG 𝒜 sel).imp fun _ _ _ h _ _ _ => h
end Formalism.L2.DIV.LinkGCl
end
end
