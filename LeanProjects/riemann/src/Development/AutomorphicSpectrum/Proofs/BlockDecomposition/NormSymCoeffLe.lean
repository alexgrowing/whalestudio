import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfIntWeight

open Finset

noncomputable def symCoeff (r : ℂ) (j : ℕ) : ℂ :=
  ∑ i ∈ range (2 * j + 1), r ^ ((i : ℤ) - (j : ℤ))

theorem symCoeff_zero (r : ℂ) : symCoeff r 0 = 1 := by
  simp [symCoeff]

theorem symCoeff_succ {r : ℂ} (j : ℕ) :
    symCoeff r (j + 1) = symCoeff r j + r ^ (j + 1) + r⁻¹ ^ (j + 1) := by
  unfold symCoeff
  have e : 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 := by ring
  rw [e, sum_range_succ', sum_range_succ]
  have h1 : ∀ i : ℕ, r ^ (((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) = r ^ ((i : ℤ) - (j : ℤ)) := by
    intro i; congr 1; push_cast; ring
  simp_rw [h1]
  have h2 : r ^ (((2 * j + 1 : ℕ) : ℤ) - (j : ℤ)) = r ^ (j + 1) := by
    rw [← zpow_natCast]; congr 1; push_cast; ring
  have h3 : r ^ (((0 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) = r⁻¹ ^ (j + 1) := by
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]; congr 1
  rw [h2, h3]

theorem norm_symCoeff_le {r : ℂ} (hr : ‖r‖ = 1) (j : ℕ) :
    ‖symCoeff r j‖ ≤ 2 * (j : ℝ) + 1 := by
  unfold symCoeff
  refine (norm_sum_le _ _).trans ?_
  simp [norm_zpow, hr]

theorem hasSum_symCoeff {r X : ℂ} (hr : ‖r‖ = 1) (hX : ‖X‖ < 1) :
    HasSum (fun j : ℕ => symCoeff r j * X ^ j) ((1 + X) / ((1 - r * X) * (1 - r⁻¹ * X))) := by
  have r0 : r ≠ 0 := by
    intro h; simp [h] at hr
  have hrX : ‖r * X‖ < 1 := by simpa [hr] using hX
  have hrX' : ‖r⁻¹ * X‖ < 1 := by simpa [hr] using hX
  have hsum : Summable (fun j : ℕ => symCoeff r j * X ^ j) := by
    have g1 : Summable (fun j : ℕ => (j : ℝ) ^ 1 * ‖X‖ ^ j) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa using hX)
    have g0 : Summable (fun j : ℕ => ‖X‖ ^ j) :=
      summable_geometric_of_lt_one (norm_nonneg _) hX
    refine Summable.of_norm_bounded ((g1.mul_left 2).add g0) ?_
    intro j
    rw [norm_mul, norm_pow]
    have := mul_le_mul_of_nonneg_right (norm_symCoeff_le hr j) (pow_nonneg (norm_nonneg X) j)
    simpa [add_mul, mul_assoc] using this
  have hS := hsum.hasSum
  set S := ∑' j : ℕ, symCoeff r j * X ^ j with hSdef
  have hA := hasSum_geometric_of_norm_lt_one hrX
  have hB := hasSum_geometric_of_norm_lt_one hrX'
  have hS1 := (hasSum_nat_add_iff' 1).2 hS
  have hA1 := (hasSum_nat_add_iff' 1).2 hA
  have hB1 := (hasSum_nat_add_iff' 1).2 hB
  have hC := ((hS.mul_right X).add hA1).add hB1
  have hfun : (fun j : ℕ => symCoeff r (j + 1) * X ^ (j + 1)) =
      fun j : ℕ => symCoeff r j * X ^ j * X + (r * X) ^ (j + 1) + (r⁻¹ * X) ^ (j + 1) := by
    funext j
    rw [symCoeff_succ, mul_pow, mul_pow, pow_succ X j]
    ring
  rw [hfun] at hS1
  have key := hS1.unique hC
  simp only [range_one, sum_singleton, symCoeff_zero, pow_zero, mul_one] at key
  have n1 : (1 - r * X) ≠ 0 := by
    intro h
    have : r * X = 1 := by linear_combination -h
    simp [this] at hrX
  have n2 : (1 - r⁻¹ * X) ≠ 0 := by
    intro h
    have : r⁻¹ * X = 1 := by linear_combination -h
    simp [this] at hrX'
  have n3 : (1 - X) ≠ 0 := by
    intro h
    have : X = 1 := by linear_combination -h
    simp [this] at hX
  have val : S = (1 + X) / ((1 - r * X) * (1 - r⁻¹ * X)) := by
    have hk : (1 - X) * S = (1 - r * X)⁻¹ + (1 - r⁻¹ * X)⁻¹ - 1 := by
      linear_combination key
    have hq : (1 - r * X)⁻¹ + (1 - r⁻¹ * X)⁻¹ - 1
        = (1 - X) * ((1 + X) / ((1 - r * X) * (1 - r⁻¹ * X))) := by
      have hru : r * r⁻¹ = 1 := mul_inv_cancel₀ r0
      have hab : (1 - r⁻¹ * X) + (1 - r * X) - (1 - r * X) * (1 - r⁻¹ * X) = (1 - X) * (1 + X) := by
        linear_combination (-X ^ 2) * hru
      generalize (1 - r * X) = a at n1 hab ⊢
      generalize (1 - r⁻¹ * X) = b at n2 hab ⊢
      field_simp
      linear_combination hab
    exact mul_left_cancel₀ n3 (hk.trans hq)
  rwa [val] at hS

theorem localSeries : E2b := by
  intro r X hr hX
  have r0 : r ≠ 0 := by
    intro h; simp [h] at hr
  have n3 : (1 - X) ≠ 0 := by
    intro h
    have : X = 1 := by linear_combination -h
    simp [this] at hX
  have hterm : (fun j : ℕ => (∑ i ∈ range (2 * j + 1), r ^ i) * (r⁻¹ * X) ^ j) =
      fun j : ℕ => symCoeff r j * X ^ j := by
    funext j
    rw [mul_pow, ← mul_assoc]
    congr 1
    unfold symCoeff
    rw [sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [zpow_sub₀ r0, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]
  have hval : (1 - X ^ 2) * ((1 - r * X)⁻¹ * (1 - X)⁻¹ * (1 - r⁻¹ * X)⁻¹) =
      (1 + X) / ((1 - r * X) * (1 - r⁻¹ * X)) := by
    have hc := mul_inv_cancel₀ n3
    rw [div_eq_mul_inv, mul_inv]
    linear_combination ((1 + X) * (1 - r * X)⁻¹ * (1 - r⁻¹ * X)⁻¹) * hc
  rw [hterm, hval]
  exact hasSum_symCoeff hr hX

end GlobalTheory.CompanionTheory.HalfIntWeight
