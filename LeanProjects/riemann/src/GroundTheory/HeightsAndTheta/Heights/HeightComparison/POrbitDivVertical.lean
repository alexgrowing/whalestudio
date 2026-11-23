import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDivVertical
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem exists_int_poly_coeff_zero_ne_zero {τ : AlgebraicClosure ℚ} (hτ : τ ≠ 0) :
    ∃ P : Polynomial ℤ, P.coeff 0 ≠ 0 ∧ Polynomial.aeval τ P = 0 := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  obtain ⟨Q, hQ, hQτ⟩ :=
    ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic τ⁻¹).restrictScalars (R := ℤ)
  have : Invertible τ⁻¹ := invertibleOfNonzero (inv_ne_zero hτ)
  refine ⟨Q.reverse, by rw [Polynomial.coeff_zero_reverse]; exact Polynomial.leadingCoeff_ne_zero.mpr hQ, ?_⟩
  have h := (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap ℤ (AlgebraicClosure ℚ)) τ⁻¹ Q).mpr hQτ
  rwa [invOf_eq_inv, inv_inv] at h

theorem OrbitDivVertical.proof : OrbitDivVertical.Statement := by
  intro ι _ _ _ n A x s _ hs V hV hH
  obtain ⟨a, -, hsa, hsW⟩ := hs
  obtain ⟨hVmin, hVrel⟩ := hV
  have hVp : V.IsPrime := hVmin.1.1
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hsV : s ∈ V := hVmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  choose c hc using hVrel
  set M : MvPolynomial (Coord n) ℤ := chartMonomial c a with hMdef
  have hMV : M ∉ V := by
    rw [hMdef, chartMonomial]
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hVp)).mp h
    exact hc k (hVp.mem_of_pow_mem _ hk)
  have hMa : Geo.IsMultiHomog (ι := blockIdx n) M a :=
    (geoMultiHomog_iff _ a).mpr (isWeightedHomogeneous_chartMonomial c a)
  set y := flatCone x
  set T : MvPolynomial ι (AlgebraicClosure ℚ) := ∏ k, X k ^ a k
  set σ := eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) y s
  set μ := eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) y M
  have hφs : Geo.mConeMap (ι := blockIdx n) y s = C σ * T := mConeMap_of_isMultiHomog y s a hsa
  have hφM : Geo.mConeMap (ι := blockIdx n) y M = C μ * T := mConeMap_of_isMultiHomog y M a hMa
  have hσ : σ ≠ 0 := fun h ↦ hsW (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, hφs, h, map_zero, zero_mul])
  have hμ : μ ≠ 0 := fun h ↦ hMV (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, hφM, h, map_zero, zero_mul]))
  obtain ⟨P, hP0, hP⟩ := exists_int_poly_coeff_zero_ne_zero (div_ne_zero hσ hμ)
  set m := P.natDegree
  let f : ℕ → MvPolynomial (Coord n) ℤ := fun j ↦ C (P.coeff j) * s ^ j * M ^ (m - j)
  have hfW : ∑ j ∈ Finset.range (m + 1), f j ∈ orbitIdeal x := by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, map_sum]
    have hterm : ∀ j ∈ Finset.range (m + 1), Geo.mConeMap (ι := blockIdx n) y (f j) =
        C (algebraMap ℤ (AlgebraicClosure ℚ) (P.coeff j) * (σ / μ) ^ j * μ ^ m) * T ^ m := by
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have e1 : (σ / μ) ^ j * μ ^ m = σ ^ j * μ ^ (m - j) := by
        rw [← Nat.add_sub_cancel' hjm, pow_add, Nat.add_sub_cancel_left, div_pow, ← mul_assoc,
          div_mul_cancel₀ _ (pow_ne_zero _ hμ)]
      have e2 : T ^ m = T ^ j * T ^ (m - j) := by rw [← pow_add, Nat.add_sub_cancel' hjm]
      simp only [f, map_mul, map_pow, hφs, hφM, MvPolynomial.algHom_C, mul_assoc, e1, e2]
      simp only [eq_intCast, map_intCast, mul_pow]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum, ← Finset.sum_mul]
    have hPτ : ∑ j ∈ Finset.range (m + 1), algebraMap ℤ (AlgebraicClosure ℚ) (P.coeff j) *
        (σ / μ) ^ j = 0 := by
      rw [← hP, Polynomial.aeval_eq_sum_range]
      simp [Algebra.smul_def]
      rfl
    rw [hPτ, zero_mul, map_zero, zero_mul]
  have hrest : ∑ j ∈ Finset.range m, f (j + 1) ∈ V :=
    Ideal.sum_mem _ fun j _ ↦ by
      simp only [f]
      rw [pow_succ]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hsV))
  have h0 : f 0 ∈ V := by
    have h := Ideal.sub_mem V (hWV hfW) hrest
    rwa [Finset.sum_range_succ', add_sub_cancel_left] at h
  simp only [f, pow_zero, mul_one, Nat.sub_zero] at h0
  rcases hVp.mem_or_mem h0 with hC | hM
  · apply hP0
    have : P.coeff 0 ∈ V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := hC
    rw [show V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) = ⊥ from hH] at this
    exact (Ideal.mem_bot).mp this
  · exact hMV (hVp.mem_of_pow_mem _ hM)

end GroundTheory.Heights₂.Heights
