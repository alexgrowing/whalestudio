import Formalism.FlagUnipotentLattices.ConductorCharacterLeakBound
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SuperdiagonalAdditionInvariance

namespace Formalism.HermitianLatticeCounting.P

open Formalism.HermitianLatticeCounting.S4 Formalism.HermitianLatticeCounting.P.S4aux Finset

theorem geometric_powers_bound : Formalism.HermitianLatticeCounting.S4.GeomPowers := by
  intro q k N hq hk
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hx : (2 : ℝ) ≤ (q : ℝ) ^ (k - 1) := by
    calc (2 : ℝ) ≤ q := hq2
      _ = (q : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (q : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have e : ∀ i : ℕ, ((q : ℝ) ^ i) ^ (k - 1) = ((q : ℝ) ^ (k - 1)) ^ i := fun i => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [e]
  have := geo_q _ hx N
  linarith

theorem hermitian_assembly_numeric_bound : Formalism.HermitianLatticeCounting.S4.WeightedAmplitudeSqSumBoundTwoTypeClasses := by
  intro k r q H nn D Ty _ _ w amp μ be isBe hk hq hH hqH hnn hw hTy hbe hμ hμbe hμal hsum hamp hampbe
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 2 * r + 5 := ⟨k - 2 * r - 5, by omega⟩
  have hq0 : (0 : ℝ) < q := by positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have e1 : (q : ℝ) ^ (-(((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 5)) = ((q : ℝ) ^ K)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  have e2 : (q : ℝ) ^ (1 - (((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 3)) = ((q : ℝ) ^ (K + 1))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  rw [e1]; rw [e2] at hampbe
  have e3 : K + 2 * r + 5 - 1 = K + (2 * r + 4) := by omega
  rw [e3] at hμbe hμal hsum
  set n : ℕ := K + (2 * r + 4) with hn
  set A0 : ℝ := H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0
  set A1 : ℝ := H ^ (4 * (r + 1)) with hA1
  have hA0p : 0 < A0 := by positivity
  have hA1p : 0 < A1 := by positivity
  by_cases hne : Nonempty Ty
  swap
  · have : IsEmpty Ty := not_nonempty_iff.1 hne
    simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
    positivity
  have hqH' := hqH hne
  have per : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ 392 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn := by
    intro t
    have hbe0 : 0 < be t := lt_of_lt_of_le one_pos (hbe t)
    obtain ⟨ε, X, hε0, hX0, hε, hX, hεb⟩ : ∃ ε X : ℝ, 0 ≤ ε ∧ 0 ≤ X ∧ (∀ d, ‖amp t d‖ ≤ ε * μ t d) ∧
        (∀ d, μ t d ≤ 2 * A0 * X) ∧ ε ^ 2 * (X * (be t ^ n)⁻¹) ≤ 49 * ((q : ℝ) ^ K)⁻¹ := by
      by_cases hb : isBe t
      · refine ⟨7 * ((q : ℝ) ^ (K + 1))⁻¹, be t ^ n, by positivity, by positivity,
          fun d => hampbe t d hb, fun d => hμbe t d hb, ?_⟩
        have h1 : be t ^ n * (be t ^ n)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
        rw [h1, mul_one, mul_pow]
        have h3 : (((q : ℝ) ^ (K + 1))⁻¹) ^ 2 ≤ ((q : ℝ) ^ K)⁻¹ := by
          rw [inv_pow, ← pow_mul]
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_right₀ hq1 (by omega)
        nlinarith
      · refine ⟨1, (be t / q) ^ n, zero_le_one, by positivity, fun d => by rw [one_mul]; exact hamp t d,
          fun d => hμal t d hb, ?_⟩
        have h2 : (be t / q) ^ n * (be t ^ n)⁻¹ = ((q : ℝ) ^ n)⁻¹ := by
          rw [div_pow]; field_simp
        have h3 : ((q : ℝ) ^ n)⁻¹ ≤ ((q : ℝ) ^ K)⁻¹ := by
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_right₀ hq1 (by omega)
        have h4 : 0 < ((q : ℝ) ^ K)⁻¹ := by positivity
        rw [h2]
        nlinarith
    have hms := S4aux.maximal_sum_bound D w (μ t) (amp t) ε (2 * A0 * X) hw (hμ t) hε0 hε hX
    calc _ ≤ _ := hms
      _ ≤ ε ^ 2 * (2 * A0 * X) * (4 * A1 * (be t ^ n)⁻¹ * nn) := by
          gcongr; exact hsum t
      _ = (ε ^ 2 * (X * (be t ^ n)⁻¹)) * (8 * A0 * A1 * nn) := by ring
      _ ≤ (49 * ((q : ℝ) ^ K)⁻¹) * (8 * A0 * A1 * nn) := by gcongr
      _ = _ := by ring
  have h392 : (392 : ℝ) ≤ H ^ 9 := by
    calc (392 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ H ^ 9 := by
          gcongr
          refine le_trans ?_ hqH'
          exact_mod_cast hq
  have hexp : (r + 2) + (r + 2) + 9 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1) ≤ 39 * (r + 1) ^ 2 := by
    nlinarith
  calc _ ≤ _ := S4aux.type_cauchy_schwarz D Ty w amp hw
    _ ≤ H ^ (r + 2) * ∑ t : Ty, 392 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn := by
        gcongr with t
        · exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun d _ => mul_nonneg (hw d) (sq_nonneg _)
        · exact per t
    _ = (Fintype.card Ty : ℝ) * (H ^ (r + 2) * (392 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ H ^ (r + 2) * (H ^ (r + 2) * (H ^ 9 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        gcongr
    _ = H ^ ((r + 2) + (r + 2) + 9 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1)) * ((q : ℝ) ^ K)⁻¹ * nn := by
        rw [pow_add, pow_add, pow_add, pow_add]; ring
    _ ≤ _ := by
        gcongr

theorem non_generic_bound_large_height : Formalism.HermitianLatticeCounting.S4.NonGenericBoundLargeHeight := by
  intro k r H nn D Ty _ _ w amp μ be hH hnn hw hTy hbe hμ hμM hsum hamp
  have hH1 : (1 : ℝ) ≤ H := by linarith
  set n : ℕ := k - 1 with hn
  set A0 : ℝ := H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0
  set A1 : ℝ := H ^ (4 * (r + 1)) with hA1
  have hA0p : 0 < A0 := by positivity
  have hA1p : 0 < A1 := by positivity
  have per : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ 8 * A0 * A1 * nn := by
    intro t
    have hbe0 : 0 < be t := lt_of_lt_of_le one_pos (hbe t)
    have hms := S4aux.maximal_sum_bound D w (μ t) (amp t) 1 (2 * A0 * be t ^ n) hw (hμ t) zero_le_one
      (fun d => by rw [one_mul]; exact hamp t d) (hμM t)
    have h1 : be t ^ n * (be t ^ n)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    calc _ ≤ _ := hms
      _ ≤ 1 ^ 2 * (2 * A0 * be t ^ n) * (4 * A1 * (be t ^ n)⁻¹ * nn) := by
          gcongr; exact hsum t
      _ = (be t ^ n * (be t ^ n)⁻¹) * (8 * A0 * A1 * nn) := by ring
      _ = _ := by rw [h1, one_mul]
  have h8 : (8 : ℝ) ≤ H ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ H ^ 3 := by gcongr
  have hexp : 1 + 1 + 3 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1) ≤ 39 * (r + 1) ^ 2 := by
    nlinarith
  calc _ ≤ _ := S4aux.type_cauchy_schwarz D Ty w amp hw
    _ ≤ H * ∑ t : Ty, 8 * A0 * A1 * nn := by
        gcongr with t
        · exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun d _ => mul_nonneg (hw d) (sq_nonneg _)
        · exact per t
    _ = (Fintype.card Ty : ℝ) * (H * (8 * A0 * A1 * nn)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ H * (H * (H ^ 3 * A0 * A1 * nn)) := by
        gcongr
    _ = H ^ (1 + 1 + 3 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1)) * nn := by
        rw [pow_add, pow_add, pow_add, pow_add, pow_one]; ring
    _ ≤ _ := by
        gcongr

end Formalism.HermitianLatticeCounting.P
