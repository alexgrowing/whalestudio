import Formalism.BranchSandwichDivisors.StatementL
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

namespace Formalism.BranchingDeterminantCap

theorem boundsIVal_of (hI : BoundsI) : BoundsIVal := by
  intro K _ _ _ _ K0 hK0 v0 hv0 n' n D H' E I0 hH hE hHE hI0 hrange hK0H hpos P hP A Bd hA G dG hG hdG hdual hBd w e he
  obtain ⟨hlat, hdual'⟩ := hI K n' n H' E I0 hH hE hHE hI0 hrange A Bd hA G dG hG hdG hdual hBd
  have key := Formalism.DivisionValues.reduction_lemma_first K K0 hK0 v0 hv0 n D (I0ᴴ * H' * I0) hK0H hpos P hP _ hlat
    (G * dG) 1 (Nat.mul_pos hG hdG) hdual' w e he
  simpa only [Nat.cast_one, one_mul] using key

end Formalism.BranchingDeterminantCap
