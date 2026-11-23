import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

def CoordLatticeFullRank.Statement (v : Basis ι E W) : Prop :=
  ∀ La : AddSubgroup W, IsLattice E La →
    (La.map (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom).FG ∧
      Submodule.span ℚ ((La.map (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom : Set (ι → E))) = ⊤

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
