import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSubLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualLatticeIndex.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i), F'.lattice ≤ F.lattice →
    (dualLattice F).toAddSubgroup.relIndex (dualLattice F').toAddSubgroup =
      F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup

example : HermLattice.twiceStandardExample.lattice ≤ (HermLattice.standard ℚ 1).lattice :=
  twiceStandardExample_le

end

end GroundTheory.Heights₂.Heights
