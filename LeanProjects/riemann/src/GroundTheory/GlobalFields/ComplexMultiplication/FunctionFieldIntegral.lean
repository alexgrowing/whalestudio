import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.PrimeLocalization
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionGauss

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsLocalRing Polynomial WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

noncomputable section

def functionFieldCongr {F : Type*} [Field F] {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.FunctionField ≃+* V'.toAffine.FunctionField := by
  subst h
  exact RingEquiv.refl _

@[simp]
theorem functionFieldCongr_self {F : Type*} [Field F] {V : WeierstrassCurve F} (h : V = V)
    (x : V.toAffine.FunctionField) : functionFieldCongr h x = x :=
  rfl

variable {L : Type*} [Field L] [NumberField L]

end

end GroundTheory.Global
