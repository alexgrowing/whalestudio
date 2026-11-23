import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Transitive

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def HyperbolicPairTransitive.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v w v' w' : W, IsHyperbolicPair h v w → IsHyperbolicPair h v' w' →
    ∃ g : h.unitaryGroup, g • v = v' ∧ g • w = w'

end Transitive

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
