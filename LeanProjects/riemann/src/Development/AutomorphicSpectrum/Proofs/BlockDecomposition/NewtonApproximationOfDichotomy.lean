import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialRootsOfClosedQuotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedUnitCoefficientRootStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonPolygonSlopeExistenceStatement

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonStep

theorem isUnit_or_of_add_quot {S : Type} [CommRing S] (ϖ : S)
    (hj : ϖ ∈ (⊥ : Ideal S).jacobson) (hD : Dich ϖ) (a b : S ⧸ Ideal.span {ϖ ^ 2})
    (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨w', hw'⟩ := h.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w'
  have h1 : (a + b) * w - 1 ∈ Ideal.span {ϖ ^ 2} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_add, map_one]
    rw [hw', sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp h1
  have hu : IsUnit ((a + b) * w) := by
    have h2 := (Ideal.mem_jacobson_bot.mp hj) (ϖ * v)
    have e : (a + b) * w = ϖ * (ϖ * v) + 1 := by linear_combination hv
    rw [e]; exact h2
  have hab : IsUnit (a + b) := isUnit_of_mul_isUnit_left hu
  have hspan : ϖ ^ 0 ∈ Ideal.span {a, b} := by
    obtain ⟨t, ht⟩ := hab.exists_right_inv
    have h3 : (a + b) * t ∈ Ideal.span {a, b} :=
      Ideal.mul_mem_right _ _ (Ideal.add_mem _ (Ideal.subset_span (by simp))
        (Ideal.subset_span (by simp)))
    rw [ht] at h3
    simpa using h3
  rcases hD a b ⟨0, hspan⟩ with h4 | h4
  · right
    exact (isUnit_of_dvd_unit (dvd_add h4 dvd_rfl) hab).map _
  · left
    exact (isUnit_of_dvd_unit (dvd_add dvd_rfl h4) hab).map _

theorem step_comp : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S ⧸ Ideal.span {ϖ ^ 2}) → Step ϖ := by
  intro S _ ϖ hj hnz hD hA Q n hQ hd hn
  have hRoots : Roots ϖ := GlobalTheory.T.polynomial_roots_of_closed_quotient ϖ hj hnz hD hA
  have hq0 : Q.coeff 0 = Q.eval 0 := Polynomial.coeff_zero_eq_eval_zero Q
  have hspan : ϖ ^ (n + 1) ∈ Ideal.span {Q.coeff 0, ϖ ^ (n + 1)} :=
    Ideal.subset_span (by simp)
  rcases hD (Q.coeff 0) (ϖ ^ (n + 1)) ⟨n + 1, hspan⟩ with hdiv | hdiv
  · refine ⟨0, ?_, ?_⟩
    · rw [← hq0]; exact hdiv
    · rw [zero_pow hd.ne']; exact dvd_zero _
  ·
    have hpow : ϖ ^ (n + 1) ∈ nonZeroDivisors S := pow_mem hnz _
    have hcancel : ∀ x : S, Q.coeff 0 * x = 0 → x = 0 := by
      intro x hx
      obtain ⟨e, he⟩ := hdiv
      have h0 : ϖ ^ (n + 1) * x = 0 := by
        rw [he]; linear_combination e * hx
      exact (mem_nonZeroDivisors_iff_right.mp hpow) x (by rw [mul_comm]; exact h0)
    obtain ⟨c, hc1, i0, hi1, hi2, hi3⟩ := GlobalTheory.T.newton_polygon_slope_existence ϖ hD hRoots (fun i => Q.coeff i)
      Q.natDegree (n + 1) hd hQ.coeff_natDegree hdiv
    have hs : ∀ i, ∃ t, (i = 0 → t = 1) ∧
        (i ≤ Q.natDegree → Q.coeff i * c ^ i = Q.coeff 0 * t) := by
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact ⟨1, fun _ => rfl, fun _ => by simp⟩
      · by_cases hid : i ≤ Q.natDegree
        · obtain ⟨t, ht⟩ := hc1 i hi hid
          exact ⟨t, fun h => by omega, fun _ => ht⟩
        · exact ⟨0, fun h => by omega, fun h => by omega⟩
    choose s hs0 hsd using hs
    have hunit : IsUnit (s i0) := by
      obtain ⟨t, ht⟩ := hi3
      have h5 : Q.coeff 0 * (s i0 * t - 1) = 0 := by
        have h6 := hsd i0 hi2
        rw [h6] at ht
        linear_combination -ht
      have h7 := hcancel _ h5
      exact IsUnit.of_mul_eq_one t (by linear_combination h7)
    let R : Polynomial S := ∑ i ∈ Finset.range (Q.natDegree + 1),
      Polynomial.C (s i) * Polynomial.X ^ i
    have hRc : ∀ j, j ≤ Q.natDegree → R.coeff j = s j := by
      intro j hj'
      simp only [R, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq]
      simp [Nat.lt_succ_of_le hj']
    have hRe : ∀ y, R.eval y = ∑ i ∈ Finset.range (Q.natDegree + 1), s i * y ^ i := by
      intro y
      simp [R, Polynomial.eval_finsetSum]
    let P : Polynomial (S ⧸ Ideal.span {ϖ ^ 2}) := R.map (Ideal.Quotient.mk _)
    have hP0 : P.coeff 0 = 1 := by
      simp only [P, Polynomial.coeff_map]
      rw [hRc 0 (Nat.zero_le _), hs0 0 rfl, map_one]
    have hPi : IsUnit (P.coeff i0) := by
      simp only [P, Polynomial.coeff_map]
      rw [hRc i0 hi2]
      exact hunit.map _
    obtain ⟨y', hy'⟩ := GlobalTheory.T.absolutely_closed_unit_coefficient_root hA (isUnit_or_of_add_quot ϖ hj hD) P i0 hP0 hi1 hPi
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
    have hRy : ϖ ^ 2 ∣ R.eval y := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
      simp only [P, Polynomial.eval_map] at hy'
      rwa [Polynomial.eval₂_at_apply] at hy'
    have hQz : Q.eval (c * y) = Q.coeff 0 * R.eval y := by
      rw [Polynomial.eval_eq_sum_range, hRe, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have h8 := hsd i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      rw [mul_pow]
      linear_combination (y ^ i) * h8
    have hn0 : ϖ ^ n ∣ Q.coeff 0 := by rw [hq0]; exact hn
    refine ⟨c * y, ?_, ?_⟩
    · rw [hQz]
      have h9 : ϖ ^ n * ϖ ^ 2 ∣ Q.coeff 0 * R.eval y := mul_dvd_mul hn0 hRy
      refine dvd_trans ?_ h9
      rw [← pow_add]
      exact pow_dvd_pow _ (by omega)
    · have h10 : Q.coeff 0 ∣ c ^ Q.natDegree := by
        have h11 := hc1 Q.natDegree hd le_rfl
        simpa [hQ.coeff_natDegree] using h11
      rw [mul_pow]
      exact dvd_mul_of_dvd_left (dvd_trans hn0 h10) _

end GlobalTheory.CompanionTheory.NewtonStep
