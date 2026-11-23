import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeSpanOfSqEqNegPrimeStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

theorem mem_prime_sq_of_sq_mem_prime_cube {A : Type} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (Y : A) (h : Y ^ 2 ∈ P ^ 3) : Y ∈ P ^ 2 := by
  have hY : Y ∈ P := hP.mem_of_pow_mem 2 (Ideal.pow_le_self (by norm_num) h)
  have hprime : Prime P := Ideal.prime_of_isPrime hP0 hP
  have hdvd : P ∣ Ideal.span {Y} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hY)
  obtain ⟨J, hJ⟩ := hdvd
  have h2 : P ^ 3 ∣ Ideal.span {Y} ^ 2 := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr h)
  rw [hJ, mul_pow, show P ^ 3 = P ^ 2 * P by ring] at h2
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero _ hP0
  have h3 : P ∣ J ^ 2 := (mul_dvd_mul_iff_left hP2).mp h2
  have h4 : P ∣ J := hprime.dvd_of_dvd_pow h3
  have h5 : P ^ 2 ∣ Ideal.span {Y} := by
    rw [hJ, sq]; exact mul_dvd_mul_left P h4
  exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd h5)

theorem natPrime_not_mem_cube_of_isUnramifiedAt :
    ∀ (p : ℕ) (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] (x : K) (P : Ideal (𝓞 H)) [P.IsPrime], p.Prime → Module.finrank ℚ K = 2 → x ^ 2 = -(p : K) → P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P → (p : 𝓞 H) ∉ P ^ 3 := by
  intro p K H _ _ _ _ _ x P _ hp hK hx hP hunr hpP
  have hint : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (p : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hx]
  set y : 𝓞 K := ⟨x, hint⟩ with hydef
  have hy : y ^ 2 = -(p : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_neg, map_natCast]
    exact hx
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hy
    have : ((p : 𝓞 K)) = 0 := by simpa using hy.symm
    exact hp.ne_zero (by exact_mod_cast this)
  have hprime : (Ideal.span {y}).IsPrime := GlobalTheory.T.isPrime_span_of_sq_eq_neg_prime_quadratic p K y hp hK hy
  set Y : 𝓞 H := algebraMap (𝓞 K) (𝓞 H) y with hYdef
  have hpY : (p : 𝓞 H) = -(Y ^ 2) := by
    rw [hYdef, ← map_pow, hy, map_neg, map_natCast, neg_neg]
  have hY2 : Y ^ 2 ∈ P ^ 3 := by
    have := (P ^ 3).neg_mem_iff.mpr hpP
    rwa [hpY, neg_neg] at this
  have hYP2 : Y ∈ P ^ 2 := mem_prime_sq_of_sq_mem_prime_cube P hP Y hY2
  have hYP : Y ∈ P := Ideal.pow_le_self (by norm_num) hYP2
  have hyU : y ∈ P.under (𝓞 K) := by
    rw [Ideal.under_def, Ideal.mem_comap]; exact hYP
  have hU0 : P.under (𝓞 K) ≠ ⊥ := by
    intro h; rw [h, Ideal.mem_bot] at hyU; exact hy0 hyU
  have hspan : Ideal.span {y} = P.under (𝓞 K) := by
    have hmax : (Ideal.span {y}).IsMaximal :=
      hprime.isMaximal (by simpa [Ideal.span_singleton_eq_bot] using hy0)
    exact hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      ((Ideal.span_singleton_le_iff_mem _).mpr hyU)
  have he : P.ramificationIdx (𝓞 K) = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (P.under (𝓞 K)) P hU0] at he
  have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 H)) (P.under (𝓞 K)) ≤ P := Ideal.map_comap_le
  have hne := (Ideal.ramificationIdx'_ne_one_iff hle).not
  apply hne.mp (not_not.mpr he)
  rw [← hspan, Ideal.map_span, Set.image_singleton]
  exact (Ideal.span_singleton_le_iff_mem _).mpr hYP2

end GlobalTheory
