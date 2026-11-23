import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesIdealStdIndex

theorem idealLattice_toAddSubgroup {K : Type} [Field K] {k : ℕ}
    (a : Fin k → FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice a).toAddSubgroup =
      AddSubgroup.pi Set.univ fun j => (a j : Submodule (𝓞 K) K).toAddSubgroup := by
  ext x
  simp [idealLattice, Submodule.mem_pi, AddSubgroup.mem_pi]

end KLinesIdealStdIndex

open KLinesIdealStdIndex in

theorem LinesIdealStdIndex.proof (h1 : LinesGenIndexPi.Statement) (h2 : LinesStdPi.Statement) :
    LinesIdealStdIndex.Statement := by
  intro K _ _ k a
  rw [idealLattice_toAddSubgroup, h2 K k, h1 (Fin k) K]
  rfl

end GroundTheory.Heights₂.Heights
