import Mathlib

namespace GroundTheory.Global

open NumberField IsDedekindDomain Polynomial

namespace Kummer

variable {K : Type*} [Field K] [NumberField K]

theorem exists_mul_pow_integral_notMem (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0)
    (a : Kˣ) (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K))) :
    ∃ c : K, c ≠ 0 ∧ ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = a * c ^ n ∧ b ∉ v.asIdeal := by
  obtain ⟨m, hm⟩ := hav
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have ha0 : v.valuation K (a : K) ≠ 0 := by simp
  set a' : K := a * (π ^ m) ^ n with ha'
  have hva' : v.valuation K a' = 1 := by
    rw [ha', map_mul, map_pow, map_zpow₀, hπ, ← WithZero.exp_log ha0, hm]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    simp
  obtain ⟨r, d, hrd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := v) a' hva'.le
  have hd : (d : 𝓞 K) ∉ v.asIdeal := d.prop
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
    intro h
    apply hd
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mp h]
    exact zero_mem _
  refine ⟨π ^ m * algebraMap (𝓞 K) K d, mul_ne_zero (zpow_ne_zero _ hπ0) hdK,
    r * d ^ (n - 1), ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, map_mul, map_pow, ← hrd, ha']
    ring
  · rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) v]
    have h1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) v).mpr hd
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, map_mul, map_pow, ← hrd, map_mul, map_mul, map_pow, hva', h1]
    simp

variable {M : Type*} [Field M] [NumberField M] [Algebra K M]

theorem isUnramifiedAt_of_pow_eq {n : ℕ} (a : Kˣ) {α : M} (hα : α ^ n = algebraMap K M a)
    (hgen : IntermediateField.adjoin K {α} = ⊤) (v : HeightOneSpectrum (𝓞 K))
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)))
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) P := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hnv (by simp)
  obtain ⟨c, hc, b, hb, hbv⟩ := exists_mul_pow_integral_notMem v hn a hav
  set x : M := algebraMap K M c * α with hx
  have hxn : x ^ n = algebraMap K M (algebraMap (𝓞 K) K b) := by
    rw [hx, mul_pow, hα, hb, map_mul, map_pow]
    ring
  have hxint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hxn]
    exact b.isIntegral_coe.algebraMap
  let y : 𝓞 M := ⟨x, hxint⟩
  have hyx : algebraMap (𝓞 M) M y = x := rfl
  have hyb : y ^ n = algebraMap (𝓞 K) (𝓞 M) b := by
    apply FaithfulSMul.algebraMap_injective (𝓞 M) M
    rw [map_pow, hyx, hxn, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M]
  have hKx : IntermediateField.adjoin K {x} = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_simple_le_iff]
    have : α = algebraMap K M c⁻¹ * x := by
      rw [hx, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self K x)
  have hgen' : Algebra.adjoin K {algebraMap (𝓞 M) M y} = ⊤ := by
    rw [hyx, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic x), hKx, IntermediateField.top_toSubalgebra]
  have hyint : IsIntegral (𝓞 K) y := Algebra.IsIntegral.isIntegral y
  obtain ⟨g, hg⟩ : minpoly (𝓞 K) y ∣ X ^ n - C b :=
    minpoly.isIntegrallyClosed_dvd hyint (by simp [hyb])
  have hder : aeval y (derivative (minpoly (𝓞 K) y)) * aeval y g = (n : 𝓞 M) * y ^ (n - 1) := by
    have := congrArg (fun p => aeval y (derivative p)) hg
    simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_add,
      map_mul, minpoly.aeval, zero_mul, add_zero] at this
    rw [← this]
    simp
  have hnP : (n : 𝓞 M) ∉ P := by
    intro h
    apply hnv
    rw [Ideal.LiesOver.over (P := P) (p := v.asIdeal), Ideal.under, Ideal.mem_comap]
    simpa using h
  have hyP : y ∉ P := by
    intro h
    apply hbv
    have : algebraMap (𝓞 K) (𝓞 M) b ∈ P :=
      hyb ▸ Ideal.pow_mem_of_mem P h n (Nat.pos_of_ne_zero hn)
    rw [Ideal.LiesOver.over (P := P) (p := v.asIdeal), Ideal.under, Ideal.mem_comap]
    exact this
  have hfP : aeval y (derivative (minpoly (𝓞 K) y)) ∉ P := by
    intro h
    have : (n : 𝓞 M) * y ^ (n - 1) ∈ P := hder ▸ Ideal.mul_mem_right _ P h
    rcases Ideal.IsPrime.mem_or_mem ‹_› this with h1 | h1
    · exact hnP h1
    · exact hyP (Ideal.IsPrime.mem_of_pow_mem ‹_› _ h1)
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K M y hgen'
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  exact hfP (Ideal.le_of_dvd hdvd hmem)

theorem ramificationIdx_eq_one_of_pow_eq {n : ℕ} (a : Kˣ) {α : M}
    (hα : α ^ n = algebraMap K M a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)))
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver v.asIdeal] :
    P.ramificationIdx (𝓞 K) = 1 := by
  have := isUnramifiedAt_of_pow_eq a hα hgen v hnv hav P
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

theorem isUnramifiedIn_of_pow_eq {n : ℕ} (a : Kˣ) {α : M}
    (hα : α ^ n = algebraMap K M a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K))) :
    Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal := fun P _ _ =>
  isUnramifiedAt_of_pow_eq a hα hgen v hnv hav P

end Kummer

end GroundTheory.Global
