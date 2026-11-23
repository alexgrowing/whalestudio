import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVectorOrbits

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

noncomputable section

def LineIndexNeZero.Statement (E W : Type*) [Field E] [NumberField E] [AddCommGroup W] [Module E W] :
    Prop :=
  ∀ (La : AddSubgroup W) (x : W), IsLattice E La → x ∈ La → x ≠ 0 → lineIndex E La x ≠ 0

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
