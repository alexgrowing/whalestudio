import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementA

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

section general

variable {K : Type} [Field K] [NumberField K]

lemma absNorm_pos' {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    (0 : ℝ) < ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  have h1 := FractionalIdeal.absNorm_nonneg I
  have h2 : (FractionalIdeal.absNorm I : ℚ) ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h2)

lemma log_absNorm_mul {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    Real.log ((FractionalIdeal.absNorm (I * J) : ℚ) : ℝ) =
      Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) + Real.log ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
  rw [map_mul, Rat.cast_mul, Real.log_mul (absNorm_pos' hI).ne' (absNorm_pos' hJ).ne']

lemma mul_le_mul_r {A B : FractionalIdeal (𝓞 K)⁰ K} (h : A ≤ B) (C : FractionalIdeal (𝓞 K)⁰ K) :
    A * C ≤ B * C :=
  mul_le_mul' h le_rfl

lemma spanSingleton_ne_zero' {x : K} (hx : x ≠ 0) : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := by
  rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]

lemma le_one_mul {A B : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≤ 1) (hB : B ≤ 1) : A * B ≤ 1 := by
  obtain ⟨A0, rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hA
  obtain ⟨B0, rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hB
  rw [← FractionalIdeal.coeIdeal_mul]
  exact FractionalIdeal.coeIdeal_le_one

lemma valuation_algebraMap_eq (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    v.valuation K (algebraMap (𝓞 K) K r) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r))) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg hr,
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v (by simpa using hr)]

lemma valuation_eq_exp_count (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (𝓞 K)⁰ x
  simp only at hrs
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hs : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hr : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hrs
    exact mul_ne_zero hx hs0 hrs
  have hv : v.valuation K x * v.valuation K (algebraMap (𝓞 K) K s) = v.valuation K (algebraMap (𝓞 K) K r) := by
    rw [← map_mul, hrs]
  have hc : FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) +
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K s)) =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r)) := by
    rw [← FractionalIdeal.count_mul K v (spanSingleton_ne_zero' hx) (spanSingleton_ne_zero' hs0),
      FractionalIdeal.spanSingleton_mul_spanSingleton, hrs]
  rw [valuation_algebraMap_eq v hs, valuation_algebraMap_eq v hr, ← hc, neg_add, WithZero.exp_add] at hv
  exact mul_right_cancel₀ WithZero.exp_ne_zero hv

lemma le_one_of_count_nonneg {J : FractionalIdeal (𝓞 K)⁰ K} (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ FractionalIdeal.count K v J) : J ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  refine finprod_induction (· ≤ 1) le_rfl (fun a b ha hb => le_one_mul ha hb) (fun v => ?_)
  show (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v J ≤ 1
  rw [← Int.toNat_of_nonneg (h v), zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one

end general

theorem degree_algebraic : DegAlg := by
  intro K _ _ L M hL hM
  obtain ⟨hLI, hLn⟩ := hL
  obtain ⟨hMI, hMn⟩ := hM
  refine ⟨⟨mul_ne_zero hLI hMI, fun σ => mul_pos (hLn σ) (hMn σ)⟩, ?_,
    ⟨inv_ne_zero hLI, fun σ => inv_pos.mpr (hLn σ)⟩, ?_,
    fun k => ⟨⟨pow_ne_zero _ hLI, fun σ => pow_pos (hLn σ) k⟩, ?_⟩⟩
  · simp only [MLine.deg, MLine.tensor]
    rw [log_absNorm_mul hLI hMI,
      Finset.sum_congr rfl (fun σ _ => Real.log_mul (hLn σ).ne' (hMn σ).ne'), Finset.sum_add_distrib]
    ring
  · simp only [MLine.deg, MLine.dual]
    rw [map_inv₀, Rat.cast_inv, Real.log_inv,
      Finset.sum_congr rfl (fun σ _ => Real.log_inv (L.n σ)), Finset.sum_neg_distrib]
    ring
  · simp only [MLine.deg, MLine.pow]
    rw [map_pow, Rat.cast_pow, Real.log_pow,
      Finset.sum_congr rfl (fun σ _ => Real.log_pow (L.n σ) k), ← Finset.mul_sum]
    ring

theorem mem_of_loc' : MemOfLoc := by
  intro K _ _ I x hI hloc
  by_cases hx : x = 0
  · rw [hx]; exact FractionalIdeal.zero_mem I
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hge : ∀ p : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K p I ≤ FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by
    intro p
    obtain ⟨c, ⟨hc0, hcount⟩, hle⟩ := hloc p
    rw [valuation_eq_exp_count p hx, valuation_eq_exp_count p hc0, WithZero.exp_le_exp, hcount] at hle
    linarith
  set J := FractionalIdeal.spanSingleton (𝓞 K)⁰ x * I⁻¹ with hJdef
  have hJ0 : J ≠ 0 := mul_ne_zero hs (inv_ne_zero hI)
  have hJ : J ≤ 1 := by
    refine le_one_of_count_nonneg hJ0 fun p => ?_
    rw [hJdef, FractionalIdeal.count_mul K p hs (inv_ne_zero hI), FractionalIdeal.count_inv]
    linarith [hge p]
  have hJI : J * I = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
    rw [hJdef, mul_assoc, inv_mul_cancel₀ hI, mul_one]
  rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← hJI]
  calc J * I ≤ 1 * I := mul_le_mul_r hJ I
    _ = I := one_mul I

end Formalism.L2.LamCM
