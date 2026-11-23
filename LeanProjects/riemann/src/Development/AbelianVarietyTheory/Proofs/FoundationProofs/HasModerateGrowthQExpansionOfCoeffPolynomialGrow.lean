import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma pow_succ_le_factorial_mul_choose (n A : ℕ) :
    ((n : ℝ) + 1) ^ A ≤ (A.factorial : ℝ) * ((n + A).choose A : ℕ) := by
  have h := Nat.pow_succ_le_ascFactorial (n + 1) A
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at h
  exact_mod_cast h

lemma norm_qterm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-2 * π * τ.im) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma one_sub_exp_inv_le (y : ℝ) (hy : 0 < y) :
    (1 - Real.exp (-2 * π * y))⁻¹ ≤ 1 + y⁻¹ := by
  set t := 2 * π * y with ht
  have htpos : 0 < t := by positivity
  have hty : y ≤ t := by
    have : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    nlinarith
  have h1 : Real.exp (-t) ≤ (1 + t)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp t])
  have h2 : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have : t / (1 + t) = 1 - (1 + t)⁻¹ := by field_simp; ring
    linarith
  have h3 : (1 - Real.exp (-t))⁻¹ ≤ (t / (1 + t))⁻¹ := inv_anti₀ (by positivity) h2
  have h4 : (t / (1 + t))⁻¹ = 1 + t⁻¹ := by field_simp; ring
  have h5 : t⁻¹ ≤ y⁻¹ := inv_anti₀ hy hty
  have : -2 * π * y = -t := by rw [ht]; ring
  rw [this]
  linarith

lemma one_add_inv_pow_le (y : ℝ) (hy : 0 < y) (B : ℕ) :
    (1 + y⁻¹) ^ B ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
  rcases le_or_gt 1 y with h | h
  · have : 1 + y⁻¹ ≤ 2 * y := by
      have : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
      linarith
    calc (1 + y⁻¹) ^ B ≤ (2 * y) ^ B := pow_le_pow_left₀ (by positivity) this B
      _ = 2 ^ B * y ^ B := mul_pow _ _ _
      _ ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
        have : 0 ≤ (y ^ B)⁻¹ := by positivity
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) B]
  · have : 1 + y⁻¹ ≤ 2 * y⁻¹ := by
      have : 1 ≤ y⁻¹ := one_le_inv₀ hy |>.mpr h.le
      linarith
    calc (1 + y⁻¹) ^ B ≤ (2 * y⁻¹) ^ B := pow_le_pow_left₀ (by positivity) this B
      _ = 2 ^ B * (y ^ B)⁻¹ := by rw [mul_pow, inv_pow]
      _ ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
        have : 0 ≤ y ^ B := by positivity
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) B]

theorem mod_qs_of_polyB : ∀ a : ℕ → ℂ, PolyB a → Mod (qs a) := by
  intro a ⟨C, A, hC⟩
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp at this
    exact le_trans (norm_nonneg _) this
  refine ⟨C * A.factorial * 2 ^ (A + 1), A + 1, fun τ => ?_⟩
  set y := τ.im
  have hy : 0 < y := τ.im_pos
  set r := Real.exp (-2 * π * y) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    have := Real.pi_pos
    calc r < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0.le]
  have hS := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) A hrn
  have hbound : ∀ n : ℕ, ‖a n * cexp (2 * π * Complex.I * n * τ)‖ ≤
      (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) := by
    intro n
    rw [norm_mul, norm_qterm]
    have h1 := hC n
    have h2 := pow_succ_le_factorial_mul_choose n A
    calc ‖a n‖ * r ^ n ≤ C * ((n : ℝ) + 1) ^ A * r ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ C * ((A.factorial : ℝ) * ((n + A).choose A : ℕ)) * r ^ n := by
          gcongr
      _ = (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) := by ring
  have hsum2 : HasSum (fun n : ℕ => (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n))
      ((C * A.factorial) * (1 / (1 - r) ^ (A + 1))) := hS.mul_left _
  have hsumm : Summable (fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hsum2.summable
  have key : ‖qs a τ‖ ≤ (C * A.factorial) * (1 / (1 - r) ^ (A + 1)) := by
    unfold qs
    calc ‖∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * τ)‖
        ≤ ∑' n : ℕ, ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := norm_tsum_le_tsum_norm hsumm
      _ ≤ ∑' n : ℕ, (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) :=
          hsumm.tsum_le_tsum hbound hsum2.summable
      _ = _ := hsum2.tsum_eq
  have hinv : 1 / (1 - r) ^ (A + 1) ≤ 2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹) := by
    rw [one_div, ← inv_pow]
    calc ((1 - r)⁻¹) ^ (A + 1) ≤ (1 + y⁻¹) ^ (A + 1) :=
          pow_le_pow_left₀ (by have : 0 < 1 - r := by linarith
                               positivity) (one_sub_exp_inv_le y hy) _
      _ ≤ _ := one_add_inv_pow_le y hy _
  calc ‖qs a τ‖ ≤ (C * A.factorial) * (1 / (1 - r) ^ (A + 1)) := key
    _ ≤ (C * A.factorial) * (2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = C * A.factorial * 2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹) := by ring

end GlobalTheory.EisM
