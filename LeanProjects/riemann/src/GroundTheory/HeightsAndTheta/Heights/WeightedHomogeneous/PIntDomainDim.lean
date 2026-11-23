import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsIntDim
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IntDimBounds

namespace GroundTheory.Heights₂.Heights

open Algebra

theorem IntDomainDim.proof : IntDomainDim.Statement := by
  intro A _ inst _ _ hinj
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  have hfin : trdeg ℤ A < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp hfin
  rw [ht, Cardinal.toENat_nat]
  have h1 := ringKrullDim_le_trdeg_add_one_int t A hinj ht
  have h2 := le_ringKrullDim_int A hinj t ht
  push_cast at h1 h2
  exact le_antisymm h1 h2

end GroundTheory.Heights₂.Heights
