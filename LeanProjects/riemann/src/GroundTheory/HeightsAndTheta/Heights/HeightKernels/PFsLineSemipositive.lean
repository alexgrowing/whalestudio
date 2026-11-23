import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem FsLineSemipositive.proof (h₁ : FsLineSmooth.Statement) (h₂ : FsLineLevi.Statement) :
    FsLineSemipositive.Statement := by
  intro K _ ι _ P
  exact ⟨h₁ K ι, fun z hz w _ => h₂ K ι z w hz.1⟩

end GroundTheory.Heights₂.Heights
