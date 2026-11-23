import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalFrameOfAnisotropicFiniteLengths
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalFrame_of_anisotropicFiniteLengths : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], AnisoSmall E → OrthoSmall E := by
  first | exact @GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall | exact GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall | (intros; apply GlobalTheory.SmoothForms.orthoSmall_of_anisoSmall <;> assumption)
