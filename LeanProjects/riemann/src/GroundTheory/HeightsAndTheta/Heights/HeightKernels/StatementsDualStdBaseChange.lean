import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualStdBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine (HermLattice.standard K i) b hb) =
      (Module.finrank ℚ K : ℝ) * II Unit (PBlk i) ⊥ i (fun _ => fsMulti (PBlk i))

example : ∃ (b : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ 1)))
    (_ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ 1 :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, le_rfl⟩

example : HermLine (dualBlocks Unit) × HermLine (PBlk 1) :=
  ⟨dualLine (HermLattice.standard ℚ 1) dualBasisStandard dualEmbMatrix_standard_bijective, fsMulti (PBlk 1)⟩

example : (fsMulti (PBlk 1)).h (fun _ => 1) = 1 := by
  simp [fsMulti, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

end

end GroundTheory.Heights₂.Heights
