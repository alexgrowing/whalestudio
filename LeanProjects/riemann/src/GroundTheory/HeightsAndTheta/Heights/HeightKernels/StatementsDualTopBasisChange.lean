import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualEmbBijective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def DualTopBasisChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T₂ : Type) [Fintype T]
    [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b₂ : Module.Basis T₂ ℤ (dualLattice F))
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T₂) (dualIdeal b₂) i (fun _ => dualLine F b₂ hb₂) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb)

def dualBasisStandardNeg : Module.Basis (Fin 1) ℤ (dualLattice (HermLattice.standard ℚ 1)) :=
  (dualBasisStandard.map (LinearEquiv.neg ℤ)).reindex (Equiv.ofUnique Unit (Fin 1))

example : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix dualBasisStandard)) ∧
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix dualBasisStandardNeg)) ∧ 1 ≤ 1 ∧
    (dualBasisStandardNeg 0 : Fin 1 → ℚ) ≠ (dualBasisStandard () : Fin 1 → ℚ) := by
  refine ⟨dualEmbMatrix_standard_bijective, DualEmbBijective.proof ℚ 1 _ _ _, le_rfl, fun h => ?_⟩
  have h0 := congrFun h 0
  simp [dualBasisStandardNeg, dualBasisStandard_apply, oneDual] at h0
  norm_num at h0

end

end GroundTheory.Heights₂.Heights
