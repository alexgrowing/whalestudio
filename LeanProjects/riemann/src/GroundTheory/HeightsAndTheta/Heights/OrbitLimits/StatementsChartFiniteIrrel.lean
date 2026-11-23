import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Inhabit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

def ChartFiniteIrrel.Statement : Prop :=
  ∀ (K : Type u) [Fintype K] (ι : K → Type v) [∀ k, Fintype (ι k)] (F : Type w) [Field F]
    (V : Ideal (MRingOver F ι)) (f : MRingOver F ι) (i : ∀ k, ι k),
    IsMultiHomogIdeal V → IsMultiHomog f (fun _ => 1) →
    (∀ W ∈ (V ⊔ Ideal.span {f}).minimalPrimes, ¬ IsRelevant W) →
    Module.Finite F (MRingOver F ι ⧸ chartIdeal V i)

end GroundTheory.Heights₂.Heights.Targets
