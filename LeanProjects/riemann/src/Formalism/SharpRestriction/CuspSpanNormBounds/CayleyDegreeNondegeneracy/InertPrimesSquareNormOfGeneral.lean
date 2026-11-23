import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InertPrimesSquareNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DifferentIdealMapNeBot

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Family

variable {eps : ℝ} (Fm : FamP eps)

def FamilyGenericTermDetProductBound (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u',
    GenericTermDetProductBound (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

end Family

end Formalism.MainNotions.BridgeLemma₂

end
