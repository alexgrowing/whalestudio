import Formalism.CharacterColumnKernels.Statement

open Finset

namespace Formalism.NG

universe uO uT uT' uΩ uR

theorem addVal_prod {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (f : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, f i) = ∑ i ∈ s, IsDiscreteValuationRing.addVal O (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

end Formalism.NG
