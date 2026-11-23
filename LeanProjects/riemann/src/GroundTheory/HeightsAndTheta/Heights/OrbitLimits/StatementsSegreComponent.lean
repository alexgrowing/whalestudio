import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Inhabit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

def SegreComponent.Statement : Prop :=
  ∀ (K : Type u) [Fintype K] (ι : K → Type v) [∀ k, Fintype (ι k)] (F : Type w) [Field F]
    (V : Ideal (MRingOver F ι)) (n : ℕ) (f : MRingOver F ι), IsProjVarF V (n + 1) →
    IsMultiHomog f (fun _ => 1) → (divSupp V f).Nonempty

end GroundTheory.Heights₂.Heights.Targets
