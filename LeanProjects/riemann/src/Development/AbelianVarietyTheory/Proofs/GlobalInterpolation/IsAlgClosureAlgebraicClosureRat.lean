import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.ScaledValuations.ValuationApplyLtOneIff
import ReciprocityTheory.GaloisValuations.GlobalB

open NumberField IsDedekindDomain

namespace GlobalTheory.V.FrobQ

instance isAlgClosure_algebraicClosure_rat : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  let i : Algebra ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instAlgebra ℚ (R := ℚ)
  have h : IsAlgClosure ℚ (AlgebraicClosure ℚ) := inferInstance
  convert h
  exact Subsingleton.elim _ _

end GlobalTheory.V.FrobQ
