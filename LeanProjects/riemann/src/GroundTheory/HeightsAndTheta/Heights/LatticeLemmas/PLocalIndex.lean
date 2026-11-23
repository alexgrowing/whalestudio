import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocalGlobalIndex
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocalLatticeIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct
open GroundTheory.Heights₂.Heights

universe u v

theorem LocalIndex.proof (h₁ : LocalGlobalIndex.Statement.{u, v})
    (h₂ : LocalLatticeIndex.Statement.{u, v}) : LocalIndex.Statement.{u, v} := by
  intro K _ _ V _ _ _ _ M₁ M₂ g hle hloc
  rw [h₁ K V M₁ M₂ hle]
  refine finprod_congr fun w ↦ ?_
  exact h₂ K V w _ _ (g w) (localLattice_isLocalLattice w M₁) (hloc w)
    (Submodule.span_mono (Set.image_mono hle))

end GroundTheory.Heights₂.Heights.LatticeLemmas
