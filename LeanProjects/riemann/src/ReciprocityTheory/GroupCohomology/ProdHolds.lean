import ReciprocityTheory.GroupCohomology.CupConnRightStatement

namespace ReciprocityTheory.Coh

open Cx Function

universe u

namespace CompatibleChartOperations

variable {R : Type u} [CommRing R]

theorem mk_eq_zero_iff {A : Cx R} {n : ℕ} (x : A.Z n) :
    (Submodule.Quotient.mk x : A.H n) = 0 ↔ x.1 ∈ A.B n := by
  rw [Submodule.Quotient.mk_eq_zero]; rfl

end CompatibleChartOperations

end ReciprocityTheory.Coh
