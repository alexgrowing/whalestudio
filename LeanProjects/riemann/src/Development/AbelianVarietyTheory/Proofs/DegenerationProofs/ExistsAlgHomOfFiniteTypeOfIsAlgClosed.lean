import Mathlib
open scoped BigOperators
open Matrix

namespace GlobalTheory

theorem exists_algHom_of_finiteType_of_isAlgClosed (K C F : Type) [Field K] [CommRing C]
    [Nontrivial C] [Algebra K C] [Algebra.FiniteType K C] [Field F] [IsAlgClosed F]
    [Algebra K F] : Nonempty (C →ₐ[K] F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  let := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing K (C ⧸ m)
  exact ⟨(IsAlgClosed.lift : (C ⧸ m) →ₐ[K] F).comp (Ideal.Quotient.mkₐ K m)⟩

end GlobalTheory
