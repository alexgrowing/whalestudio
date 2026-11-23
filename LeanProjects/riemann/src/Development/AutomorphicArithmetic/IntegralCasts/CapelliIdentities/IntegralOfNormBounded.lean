import Mathlib

open Polynomial in
private lemma UpperTheory.Reformulated.B.IntegralOfNormBounded.mem_of_mul_eq_one {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (B : Subalgebra A K) {t y : K} (hty : t * y = 1) (hy : y ∈ B) (ht : IsIntegral A t) :
    t ∈ B := by
  obtain ⟨p, hm, hp⟩ := ht
  have key : ∀ (q : A[X]) (n : ℕ), q.natDegree ≤ n → y ^ n * aeval t q ∈ B := by
    intro q n hq
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hq), Finset.mul_sum]
    refine Subalgebra.sum_mem _ fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e : y ^ n * (q.coeff i • t ^ i) = q.coeff i • y ^ (n - i) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hin
      rw [Nat.add_sub_cancel_left, mul_smul_comm, pow_add]
      congr 1
      rw [mul_comm (y ^ i), mul_assoc, ← mul_pow, mul_comm y t, hty, one_pow, mul_one]
    rw [e]
    exact Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hy _) _
  have h0 : aeval t p = 0 := hp
  have hd : p.natDegree ≠ 0 := by
    intro h
    have h1 := eq_one_of_monic_natDegree_zero hm h
    simp [h1] at h0
  obtain ⟨d, hd'⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have h2 : aeval t p.eraseLead + t ^ (d + 1) = 0 := by
    have h3 := p.eraseLead_add_C_mul_X_pow
    rw [← h3, map_add, map_mul, aeval_C, map_pow, aeval_X, hm.leadingCoeff, map_one, one_mul,
      hd'] at h0
    exact h0
  have h4 : t = -(y ^ d * aeval t p.eraseLead) := by
    have h5 : y ^ d * t ^ (d + 1) = t := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, mul_comm y t, hty, one_pow, one_mul]
    have h6 : aeval t p.eraseLead = -t ^ (d + 1) := eq_neg_of_add_eq_zero_left h2
    rw [h6, mul_neg, neg_neg, h5]
  rw [h4]
  refine neg_mem (key _ _ ?_)
  have := p.eraseLead_natDegree_le
  omega

open Polynomial in
private lemma UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le {l : ℕ} [Fact (Nat.Prime l)] {K : Type}
    [Field K] [Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [Algebra ℤ_[l] K]
    [IsScalarTower ℤ_[l] ℚ_[l] K] (z : K) (hz : spectralNorm ℚ_[l] K z ≤ 1) :
    IsIntegral ℤ_[l] z := by
  have hzi : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  have hmon := minpoly.monic hzi
  have hc := (spectralValue_le_one_iff hmon).mp hz
  have hl : minpoly ℚ_[l] z ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hmon
  refine ⟨q, hqm, ?_⟩
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K, ← eval₂_map, hq]
  exact minpoly.aeval ℚ_[l] z

theorem UpperTheory.Reformulated.B.IntegralOfNormBounded.ptc_field :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type}
    [inst_1 : CommRing R] [inst_2 : IsLocalRing R] [inst_3 : Algebra ℤ_[l] R] {K : Type} [inst_4 : Field K]
    [inst_5 : Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [inst_7 : Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    (x : R →ₐ[ℤ_[l]] K),
    ∀ a ∈ IsLocalRing.maximalIdeal R,
      IsIntegral ℤ_[l] ((x : R → K) a) ∧ ∃ (n : ℕ) (b : K), IsIntegral ℤ_[l] b ∧ (x : R → K) a ^ n = (↑l : K) * b := by
  intro l _ R _ _ _ K _ _ _ _ _ x a ha
  have hA : ∀ t : K, t * x a = 1 → ¬ IsIntegral ℤ_[l] t := by
    intro t hty ht
    obtain ⟨r, hr⟩ : t ∈ x.range :=
      UpperTheory.Reformulated.B.IntegralOfNormBounded.mem_of_mul_eq_one x.range hty ⟨a, rfl⟩ ht
    have hr' : x r = t := hr
    have hmem : a * r ∈ IsLocalRing.maximalIdeal R := Ideal.mul_mem_right _ _ ha
    have hu : IsUnit (1 - a * r) := by
      by_contra hn
      have h1 : 1 - a * r ∈ IsLocalRing.maximalIdeal R := hn
      have h2 := Ideal.add_mem _ h1 hmem
      rw [sub_add_cancel] at h2
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h2
    have h3 := hu.map x
    have h4 : x (1 - a * r) = 0 := by
      rw [map_sub, map_mul, map_one, hr', mul_comm, hty, sub_self]
    rw [h4] at h3
    exact not_isUnit_zero h3
  change IsIntegral ℤ_[l] (x a) ∧ ∃ (n : ℕ) (b : K), IsIntegral ℤ_[l] b ∧ x a ^ n = (↑l : K) * b
  generalize x a = y at hA
  by_cases hy : y = 0
  · subst hy
    exact ⟨isIntegral_zero, 1, 0, isIntegral_zero, by simp⟩
  let f := spectralMulAlgNorm ℚ_[l] K
  have hf : ∀ z, f z = spectralNorm ℚ_[l] K z := fun _ => rfl
  have hfmul : ∀ u v, f (u * v) = f u * f v := fun u v => map_mul f u v
  have hf1 : f 1 = 1 := map_one f
  have hfy : f y < 1 := by
    have h1 : ¬ f y⁻¹ ≤ 1 := fun h =>
      hA y⁻¹ (inv_mul_cancel₀ hy) (UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ h)
    have h2 : f y * f y⁻¹ = 1 := by rw [← hfmul, mul_inv_cancel₀ hy, hf1]
    have h3 : 0 ≤ f y := (hf y).symm ▸ spectralNorm_nonneg y
    push_neg at h1
    nlinarith
  have hfpow : ∀ (n : ℕ) (z : K), f (z ^ n) = f z ^ n := by
    intro n z
    induction n with
    | zero => simp [hf1]
    | succ n ih => rw [pow_succ, hfmul, ih, pow_succ]
  have hlpos : (0 : ℝ) < (l : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime l).pos
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hlpos) hfy
  have hlK : (l : K) ≠ 0 := by
    have h1 : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := by simp
    rw [h1]
    have h2 : (l : ℚ_[l]) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
    exact (map_ne_zero (algebraMap ℚ_[l] K)).mpr h2
  refine ⟨UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ hfy.le, n, y ^ n * (l : K)⁻¹,
    UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ ?_, ?_⟩
  · have h1 : f ((l : K)⁻¹) = l := by
      have h2 : (l : K)⁻¹ = algebraMap ℚ_[l] K ((l : ℚ_[l])⁻¹) := by simp
      rw [h2, hf, spectralNorm_extends, norm_inv, Padic.norm_p]
      simp
    change f (y ^ n * (l : K)⁻¹) ≤ 1
    rw [hfmul, hfpow, h1]
    calc f y ^ n * l ≤ (l : ℝ)⁻¹ * l := by gcongr
      _ = 1 := inv_mul_cancel₀ hlpos.ne'
  · field_simp
