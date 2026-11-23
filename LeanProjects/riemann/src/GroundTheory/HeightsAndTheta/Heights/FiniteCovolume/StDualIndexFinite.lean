import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def DualIndexFinite.Statement (h : HermitianForm F E W) : Prop :=
  ∀ La : AddSubgroup W, IsLattice E La → IsIntegralOn h La → La.relIndex (dualLattice h La) ≠ 0

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
