import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.TwWts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.PtPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CsdOf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem half_pow {M : Type} [CommGroup M] {x y u : M} {a e m : ℤ} {k k' : ℕ} (hm : e - a = m + m)
    (hx : (x ^ 2 * u ^ (-e)) ^ k' = 1) (hy : (y ^ 2 * u ^ (-a)) ^ k = 1) :
    (x * y⁻¹ * u ^ (-m)) ^ (2 * (k * k')) = 1 := by
  obtain rfl : e = a + m + m := by omega
  have hsq : (x * y⁻¹ * u ^ (-m)) ^ 2 = (x ^ 2 * u ^ (-(a + m + m))) * (y ^ 2 * u ^ (-a))⁻¹ := by
    rw [mul_inv, mul_mul_mul_comm, mul_pow, mul_pow, inv_pow]
    congr 1
    group
  have h1 : (x ^ 2 * u ^ (-(a + m + m))) ^ (k * k') = 1 := by
    rw [mul_comm k k', pow_mul, hx, one_pow]
  have h2 : (y ^ 2 * u ^ (-a)) ^ (k * k') = 1 := by
    rw [pow_mul, hy, one_pow]
  rw [pow_mul, hsq, mul_pow, inv_pow, h1, h2, inv_one, mul_one]
