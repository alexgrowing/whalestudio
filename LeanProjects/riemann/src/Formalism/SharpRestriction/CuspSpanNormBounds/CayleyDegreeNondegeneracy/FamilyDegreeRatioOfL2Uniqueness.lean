import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DegreeL2RangeHypothesis

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma MeasureTheory
open scoped InnerProductSpace ENNReal

section Fam

variable {eps : ℝ} (Fm : FamP eps)

def deg_L2F (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => DegreeL2RangeHypothesis (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
