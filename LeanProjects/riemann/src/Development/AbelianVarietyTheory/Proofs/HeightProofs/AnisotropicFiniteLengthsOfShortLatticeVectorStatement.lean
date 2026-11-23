import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AnisotropicFiniteLengthsOfShortLatticeVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropicFiniteLengths_of_shortLatticeVector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ShortSmall E → AnisoSmall E := by
  first | exact @GlobalTheory.AnisoSize.anisoSmall_of_shortSmall | exact GlobalTheory.AnisoSize.anisoSmall_of_shortSmall | (intros; apply GlobalTheory.AnisoSize.anisoSmall_of_shortSmall <;> assumption)
