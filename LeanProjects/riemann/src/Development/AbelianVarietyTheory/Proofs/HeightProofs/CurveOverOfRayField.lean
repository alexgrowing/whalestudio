import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardEqIffStabilizer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurve

section Quadratic

variable {K : Type} [Field K] [NumberField K] {d : ℕ}

theorem norm_int_eq (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) (a : 𝓞 K) :
    ((Algebra.norm ℤ a : ℤ) : ℝ) = ‖φ a‖ ^ 2 := by
  rw [← GlobalTheory.QuadraticZeta.norm_eq_sq h2 hD φ, ← Algebra.coe_norm_int, Rat.cast_intCast]

theorem sq_ne_prime (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) {p : ℕ} (hp : p.Prime)
    (a : 𝓞 K) : a * a ≠ p := by
  intro h
  have h1 : φ a * φ a = p := by
    rw [← map_mul]
    have := congrArg (fun x : 𝓞 K => φ x) h
    simpa using this
  have hre := congrArg Complex.re h1
  have him := congrArg Complex.im h1
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im] at hre him
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hi : (φ a).im = 0 := by
    by_contra hi
    have : (φ a).re = 0 := mul_right_cancel₀ hi (by linarith)
    rw [this] at hre
    nlinarith [mul_self_nonneg (φ a).im]
  have h3 := norm_int_eq h2 hD φ (a + 1)
  rw [Complex.sq_norm, Complex.normSq_apply] at h3
  simp only [map_add, map_one, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, hi] at h3
  generalize Algebra.norm ℤ (a + 1) = m at h3
  rw [hi] at hre
  have h4 : Irrational (φ a).re := by
    have h5 := hp.irrational_sqrt
    rw [← hre, mul_zero, sub_zero, Real.sqrt_mul_self_eq_abs] at h5
    rcases abs_choice (φ a).re with h | h <;> rw [h] at h5
    · exact h5
    · exact h5.of_neg
  refine h4 ⟨((m : ℚ) - p - 1) / 2, ?_⟩
  push_cast
  linarith

theorem span_isPrime (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) {p : ℕ} (hp : p.Prime)
    {a : 𝓞 K} (ha : ‖φ a‖ ^ 2 = p) : (Ideal.span {a}).IsPrime := by
  refine Ideal.isPrime_of_irreducible_absNorm ?_
  have : Algebra.norm ℤ a = p := by
    have := (norm_int_eq h2 hD φ a).trans ha
    exact_mod_cast this
  rw [Ideal.absNorm_span_singleton, this, Int.natAbs_natCast]
  exact hp

theorem eq_of_span_eq (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) {n : ℕ} (hn : 3 ≤ n)
    {c c' : 𝓞 K} (h0 : (1 + n * c : 𝓞 K) ≠ 0) (hnorm : ‖φ (1 + n * c' : 𝓞 K)‖ = ‖φ (1 + n * c : 𝓞 K)‖)
    (h : Ideal.span {1 + n * c} = Ideal.span {(1 + n * c' : 𝓞 K)}) : (1 + n * c : 𝓞 K) = 1 + n * c' := by
  obtain ⟨u, hu⟩ : (1 + n * c : 𝓞 K) ∣ 1 + n * c' := by
    rw [← Ideal.mem_span_singleton, h]
    exact Ideal.mem_span_singleton_self _
  have hu1 : ‖φ u‖ = 1 := by
    rw [hu] at hnorm
    simp only [map_mul, norm_mul] at hnorm
    refine (mul_eq_left₀ ?_).1 hnorm
    rw [norm_ne_zero_iff, map_ne_zero]
    exact fun h => h0 (RingOfIntegers.coe_injective (by rw [h, map_zero]))
  have ht : u - 1 = n * (c' - c * u) := by linear_combination -hu
  generalize c' - c * u = t at ht
  have h3 : (n : ℝ) * ‖φ t‖ ≤ 2 := by
    have e : (n : ℂ) * φ t = φ u - 1 := by
      have := congrArg (fun x : 𝓞 K => φ x) ht
      simpa using this.symm
    have := norm_sub_le (φ u) 1
    rw [← e, norm_mul, Complex.norm_natCast, hu1, norm_one] at this
    linarith
  have h4 := norm_int_eq h2 hD φ t
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : ‖φ t‖ < 1 := by nlinarith [norm_nonneg (φ t)]
  have h6 : Algebra.norm ℤ t = 0 := by
    have a1 : ((Algebra.norm ℤ t : ℤ) : ℝ) < 1 := by nlinarith [norm_nonneg (φ t)]
    have a2 : (0 : ℝ) ≤ (Algebra.norm ℤ t : ℤ) := by rw [h4]; positivity
    have a3 : Algebra.norm ℤ t < 1 := by exact_mod_cast a1
    have a4 : 0 ≤ Algebra.norm ℤ t := by exact_mod_cast a2
    omega
  rw [Algebra.norm_eq_zero_iff] at h6
  rw [h6, mul_zero, sub_eq_zero] at ht
  rw [hu, ht, mul_one]

theorem ncard_eq_finrank [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ)
    {n : ℕ} (hn : 3 ≤ n) (R : Type) [Field R] [NumberField R] [Algebra K R] [IsAbelianGalois K R]
    (hR : IsRay R (Ideal.span {(n : 𝓞 K)})) {p : ℕ} (hp : p.Prime) {c c' : 𝓞 K}
    (hnorm : ‖φ (1 + n * c' : 𝓞 K)‖ = ‖φ (1 + n * c : 𝓞 K)‖) (hmul : (1 + n * c) * (1 + n * c') = (p : 𝓞 K)) :
    {v : HeightOneSpectrum (𝓞 R) | ((p : ℕ) : 𝓞 R) ∈ v.asIdeal}.ncard = Module.finrank ℚ R := by
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsq : ‖φ (1 + n * c : 𝓞 K)‖ ^ 2 = p := by
    have := congrArg (fun x : 𝓞 K => ‖φ x‖) hmul
    simp only [map_mul, norm_mul, map_natCast, Complex.norm_natCast] at this
    rw [sq]
    nth_rewrite 2 [← hnorm]
    exact this
  have key : ∀ b : 𝓞 K, ‖φ (1 + n * b : 𝓞 K)‖ ^ 2 = p → (Ideal.span {(1 + n * b : 𝓞 K)}).IsMaximal ∧
      {Q : HeightOneSpectrum (𝓞 R) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = Ideal.span {1 + n * b}}.ncard =
        Module.finrank K R := by
    intro b hb
    have hP := span_isPrime h2 hD φ hp hb
    have hne : Ideal.span {(1 + n * b : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      intro h
      rw [h] at hb
      exact hp.ne_zero (by simpa using hb.symm)
    refine ⟨hP.isMaximal hne, (RaySplit.ncard_eq_finrank_iff K R n (by omega) hR ⟨_, hP, hne⟩ fun h => ?_).2
      ⟨_, rfl, Ideal.mem_span_singleton.2 ⟨b, by ring⟩⟩⟩
    refine hP.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    have := Ideal.sub_mem _ (Ideal.mem_span_singleton_self (1 + n * b : 𝓞 K)) (Ideal.mul_mem_right b _ h)
    simpa using this
  obtain ⟨hm, hc⟩ := key c hsq
  obtain ⟨hm', hc'⟩ := key c' (by rw [hnorm, hsq])
  have hpos : Module.finrank K R ≠ 0 := Module.finrank_pos.ne'
  have hmem : ∀ (Q : HeightOneSpectrum (𝓞 R)) (a : 𝓞 K), (Ideal.span {a}).IsMaximal →
      (a ∈ Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) ↔ Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = Ideal.span {a}) := by
    intro Q a ha
    have := Q.isPrime
    refine ⟨fun h => (ha.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ((Ideal.span_singleton_le_iff_mem _).2 h)).symm,
      fun h => h ▸ Ideal.mem_span_singleton_self a⟩
  have hset : {v : HeightOneSpectrum (𝓞 R) | ((p : ℕ) : 𝓞 R) ∈ v.asIdeal} =
      {Q : HeightOneSpectrum (𝓞 R) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = Ideal.span {1 + n * c}} ∪
      {Q : HeightOneSpectrum (𝓞 R) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = Ideal.span {1 + n * c'}} := by
    ext Q
    have := Q.isPrime
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rw [← hmem Q _ hm, ← hmem Q _ hm', ← Ideal.IsPrime.mul_mem_iff_mem_or_mem inferInstance, hmul, Ideal.mem_comap,
      map_natCast]
  rw [hset, Set.ncard_union_eq ?_ (Set.finite_of_ncard_ne_zero (hc ▸ hpos)) (Set.finite_of_ncard_ne_zero (hc' ▸ hpos)),
    hc, hc', ← Module.finrank_mul_finrank ℚ K R, h2, two_mul]
  rw [Set.disjoint_left]
  intro Q h1 h1'
  have := eq_of_span_eq h2 hD φ hn (left_ne_zero_of_mul (hmul ▸ hp0)) hnorm (h1.symm.trans h1')
  rw [← this] at hmul
  exact sq_ne_prime h2 hD φ hp _ hmul

end Quadratic

theorem ncard_congr {M R : Type} [Field M] [Field R] [NumberField M] [NumberField R] (e : M ≃+* R) (p : ℕ) :
    {v : HeightOneSpectrum (𝓞 M) | ((p : ℕ) : 𝓞 M) ∈ v.asIdeal}.ncard =
      {v : HeightOneSpectrum (𝓞 R) | ((p : ℕ) : 𝓞 R) ∈ v.asIdeal}.ncard := by
  refine Set.ncard_congr' (Equiv.subtypeEquiv
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)) fun Q => ?_)
  simp [HeightOneSpectrum.equivOfRingEquiv, HeightOneSpectrum.comap, Ideal.mem_comap]

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in

theorem _root_.GlobalTheory.FieldSize.RayExistCurve.finrank_adjoin {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    FiniteDimensional ℚ ℚ⟮r⟯ ∧ Module.finrank ℚ ℚ⟮r⟯ = 2 := by
  have hroot : aeval r (X ^ 2 + C (d : ℚ)) = 0 := by simp [hr]
  have hmon : (X ^ 2 + C (d : ℚ)).Monic := monic_X_pow_add_C _ (by norm_num)
  have hint : IsIntegral ℚ r := ⟨_, hmon, by simpa [aeval_def] using hroot⟩
  have hdeg : (X ^ 2 + C (d : ℚ)).natDegree = 2 := natDegree_X_pow_add_C
  have hirr : Irreducible (X ^ 2 + C (d : ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x hx
      have hx' : x ^ 2 + (d : ℚ) = 0 := by simpa using hx
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      nlinarith [sq_nonneg x]
  have hmin : minpoly ℚ r = X ^ 2 + C (d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
  refine ⟨IntermediateField.adjoin.finiteDimensional hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]

theorem conj_eq_neg {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) : starRingEnd ℂ r = -r := by
  have h1 := congrArg Complex.re hr
  have h2 := congrArg Complex.im hr
  simp [sq] at h1 h2
  have h3 : (0 : ℝ) < d := by exact_mod_cast hd
  have h4 : r.re = 0 := by
    by_contra h
    have : r.im = 0 := mul_left_cancel₀ h (by linarith)
    rw [this] at h1
    nlinarith [mul_self_nonneg r.re]
  apply Complex.ext <;> simp [h4]

end GlobalTheory.FieldSize.RayExistCurve
