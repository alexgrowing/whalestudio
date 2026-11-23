import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormDehomIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormBadPrimesFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormGoodPrimeIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormPrimeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

namespace FibreNormDehomIntegral

theorem den_eq_one_of_padicValRat_nonneg {a : ℚ} (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p a) : a.den = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have := Fact.mk hp
  have hnum : ¬ (p : ℤ) ∣ a.num := by
    intro hn
    have h1 : p ∣ Nat.gcd a.num.natAbs a.den := Nat.dvd_gcd (Int.ofNat_dvd_left.mp hn) hpd
    rw [a.reduced.gcd_eq_one] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have h0 := h p hp
  rw [padicValRat, padicValInt.eq_zero_of_not_dvd hnum] at h0
  have h2 : 1 ≤ padicValNat p a.den := one_le_padicValNat_of_dvd a.den_ne_zero hpd
  omega

end FibreNormDehomIntegral

open FibreNormDehomIntegral in

theorem FibreNormDehomIntegral.proof (hF : FibreNormBadPrimesFinite.Statement)
    (hG : FibreNormGoodPrimeIntegral.Statement) (hB : FibreNormPrimeBound.Statement) :
    FibreNormDehomIntegral.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L q hV hBir he hL hz
  have hSf := hF K ι Ω y D e L hV hBir he hL hz
  set T := hSf.toFinset with hT
  choose! C hC using hB K ι Ω y D e L q hV hBir he hL hz
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => ((Set.Finite.mem_toFinset hSf).mp hp).1
  set M₀ : ℕ := ∏ p ∈ T, p ^ C p with hM
  have hM0 : M₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hTp p hp).ne_zero
  refine ⟨M₀, Nat.one_le_iff_ne_zero.mpr hM0, ?_⟩
  intro τ s hs j c hc

  have hcoef : ∀ m, (((M₀ : ℚ) ^ τ) * (c (Module.finrank (pullField y L) Ω)).coeff m).den = 1 := by
    intro m
    by_cases ha : (c (Module.finrank (pullField y L) Ω)).coeff m = 0
    · rw [ha, mul_zero]; rfl
    refine den_eq_one_of_padicValRat_nonneg fun p hp => ?_
    have := Fact.mk hp
    have hMq : ((M₀ : ℚ) ^ τ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hM0)
    rw [padicValRat.mul hMq ha, padicValRat.pow, padicValRat.of_nat]
    by_cases hpT : p ∈ T
    · have hle : C p ≤ padicValNat p M₀ :=
        (padicValNat_dvd_iff_le hM0).mp (Finset.dvd_prod_of_mem (fun p => p ^ C p) hpT)
      have hb := hC p hp τ s hs j c hc m
      have hle' : ((C p * τ : ℕ) : ℤ) ≤ (τ : ℤ) * (padicValNat p M₀ : ℤ) := by
        push_cast
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by positivity)
      linarith
    · have hgood : ¬ HasCommonZeroModP y L p hp := fun h =>
        hpT ((Set.Finite.mem_toFinset hSf).mpr ⟨hp, h⟩)
      have hg := hG K ι Ω y D e L q hV hBir he hL hz p hp hgood τ s hs j c hc m
      have : (0 : ℤ) ≤ (τ : ℤ) * (padicValNat p M₀ : ℤ) := by positivity
      linarith

  have hmem : ((M₀ : ℚ) ^ τ) • c (Module.finrank (pullField y L) Ω) ∈
      Set.range (map (Int.castRingHom ℚ) : MvPolynomial (Fin (D + 1)) ℤ → MvPolynomial (Fin (D + 1)) ℚ) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.mp ha
    refine ⟨(((M₀ : ℚ) ^ τ) * (c (Module.finrank (pullField y L) Ω)).coeff m).num, ?_⟩
    rw [coeff_smul, smul_eq_mul, eq_intCast]
    exact Rat.coe_int_num_of_den_eq_one (hcoef m)
  obtain ⟨F, hF'⟩ := hmem
  exact ⟨F, hF'⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
