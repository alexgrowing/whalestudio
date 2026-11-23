import Formalism.LogVandermondeBounds.LogVandermondeVariationUnbounded

namespace Formalism.LogVandermondeBounds.StandardLattice

open Polynomial

theorem primeOrderFinrank : PrimeOrderFinrank := by
  intro K _ _ n g A hg hA hA1
  haveI := Fact.mk hg
  let f : (Fin n → K) →ₗ[ℚ] (Fin n → K) := (Matrix.toLin' A).restrictScalars ℚ
  have hpow : ∀ v : Fin n → K, (f ^ g) v = v := by
    intro v
    rw [Module.End.pow_apply]
    show (⇑(Matrix.toLin' A))^[g] v = v
    rw [← Module.End.pow_apply, ← Matrix.toLin'_pow, hA, Matrix.toLin'_one, LinearMap.id_apply]
  have hfg : f ^ g = 1 := LinearMap.ext hpow
  have hint : IsIntegral ℚ f := IsIntegral.of_finite ℚ f
  have hm0 : minpoly ℚ f ≠ 0 := minpoly.ne_zero hint
  have hdvd : minpoly ℚ f ∣ Polynomial.cyclotomic g ℚ * (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hfg]
  have hirr := Polynomial.cyclotomic.irreducible_rat hg.pos
  have hdeg : (Polynomial.cyclotomic g ℚ).natDegree = g - 1 := by
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hg]
  have hle : (minpoly ℚ f).natDegree ≤ Module.finrank ℚ K * n := by
    have h1 := Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f) (LinearMap.charpoly_monic f).ne_zero
    rw [LinearMap.charpoly_natDegree] at h1
    have h2 : Module.finrank ℚ (Fin n → K) = Module.finrank ℚ K * n := by
      rw [Module.finrank_pi_fintype]
      simp [mul_comm]
    omega
  by_cases hc : Polynomial.cyclotomic g ℚ ∣ minpoly ℚ f
  · have := Polynomial.natDegree_le_of_dvd hc hm0
    omega
  · exfalso
    apply hA1
    have hcop : IsCoprime (minpoly ℚ f) (Polynomial.cyclotomic g ℚ) :=
      ((hirr.coprime_iff_not_dvd).2 hc).symm
    have h1 : minpoly ℚ f ∣ Polynomial.X - 1 := by
      first
        | exact hcop.dvd_of_dvd_mul_left hdvd
        | exact hcop.dvd_of_dvd_mul_right hdvd
        | exact hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at hdvd)
        | exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hdvd)
    have h2 : Polynomial.aeval f (Polynomial.X - 1 : Polynomial ℚ) = 0 := by
      obtain ⟨q, hq⟩ := h1
      rw [hq, map_mul, minpoly.aeval, zero_mul]
    have hf1 : f = 1 := by
      simpa [sub_eq_zero] using h2
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun hf1 v
    simpa [f] using this

theorem primePowerSubgroupTrivial : PrimePowerSubgroupTrivial := by
  intro K _ _ n g Γ hg hfin hcard hlt
  obtain ⟨e, he⟩ := hcard
  rw [Subgroup.eq_bot_iff_forall]
  intro γ hγ
  by_contra hne
  set x : Γ := ⟨γ, hγ⟩ with hxdef
  have hx : x ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have hdvd : orderOf x ∣ g ^ e := by
    rw [← he]
    exact orderOf_dvd_natCard x
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hg).1 hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hx (orderOf_eq_one_iff.1 (by simpa using hm))
  set y := x ^ (g ^ (m - 1)) with hy
  have hyg : y ^ g = 1 := by
    rw [hy, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm0), ← hm,
      pow_orderOf_eq_one]
  have hy1 : y ≠ 1 := by
    intro h
    have h3 := orderOf_dvd_of_pow_eq_one (show x ^ (g ^ (m - 1)) = 1 from h)
    rw [hm] at h3
    have := (Nat.pow_dvd_pow_iff_le_right hg.one_lt).1 h3
    omega
  have key := primeOrderFinrank K n g ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) hg
    (by rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hyg]; rfl)
    (fun h => hy1 (Subtype.ext (Units.ext (by simpa using h))))
  omega

end Formalism.LogVandermondeBounds.StandardLattice
