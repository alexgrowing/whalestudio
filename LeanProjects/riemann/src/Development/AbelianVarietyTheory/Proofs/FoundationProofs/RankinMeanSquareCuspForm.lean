import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLineStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.MeanSquareEstimates

theorem key (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ) (hc : CF k L χ h) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖qs h τ‖ ^ 2 * τ.im ^ k ≤ C) (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y)) ∧
      ∑' n : ℕ, ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y) ≤ C / y ^ k := by
  have hp := GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line h h y hc.1.1 hc.1.1 hy
  set I := ∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs h (ofComplex (x + y * Complex.I))
  have hr := Complex.hasSum_re hp
  have e : (fun n : ℕ => (conj (h n) * h n * ((Real.exp (-4 * π * n * y) : ℝ) : ℂ)).re) =
      fun n : ℕ => ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y) := by
    funext n
    rw [Complex.conj_mul']
    norm_cast
  rw [e] at hr
  refine ⟨hr.summable, ?_⟩
  rw [hr.tsum_eq]
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) 1, ‖conj (qs h (ofComplex (x + y * Complex.I))) * qs h (ofComplex (x + y * Complex.I))‖ ≤ C / y ^ k := by
    intro x _
    have him : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
    rw [ofComplex_apply_of_im_pos him, Complex.conj_mul']
    have h1 := hC ⟨(x : ℂ) + y * Complex.I, him⟩
    have h2 : (⟨(x : ℂ) + y * Complex.I, him⟩ : ℍ).im = y := by simp [UpperHalfPlane.im]
    rw [h2] at h1
    rw [le_div_iff₀ (by positivity)]
    simpa using h1
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  calc I.re ≤ ‖I‖ := Complex.re_le_norm I
    _ ≤ C / y ^ k * |1 - 0| := this
    _ = C / y ^ k := by simp

theorem key2 (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ) (hc : CF k L χ h) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖qs h τ‖ ^ 2 * τ.im ^ k ≤ C) (t : ℝ) (ht : 0 < t) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖h n‖ ^ 2 * Real.exp (-(n : ℝ) * t) ≤ C * (4 * π) ^ k / t ^ k := by
  have hy : 0 < t / (4 * π) := by positivity
  obtain ⟨hs, hb⟩ := key k L χ h hc C hC _ hy
  have e : ∀ n : ℕ, -4 * π * n * (t / (4 * π)) = -(n : ℝ) * t := fun n => by field_simp
  simp only [e] at hs hb
  have e2 : C / (t / (4 * π)) ^ k = C * (4 * π) ^ k / t ^ k := by rw [div_pow]; field_simp
  rw [e2] at hb
  exact (hs.sum_le_tsum _ (fun n _ => by positivity)).trans hb

theorem blk (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (a0 : a 0 = 0) (k : ℕ) (D : ℝ)
    (hD : ∀ t : ℝ, 0 < t → ∀ N : ℕ, ∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) * t) ≤ D / t ^ k)
    (s : ℝ) (hs : 0 < s) (N : ℕ) :
    ∑ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s)) := by
  set x : ℝ := (2 : ℝ) ^ (-s) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hD0 : 0 ≤ D := by
    have := hD 1 one_pos 0
    simpa using this
  set G : ℕ → ℕ → ℝ := fun j n => Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) * (a n * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹)) with hG
  have G0 : ∀ j n, 0 ≤ G j n := fun j n => by have := ha n; positivity
  have pt : ∀ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ ∑ j ∈ Finset.range N, G j n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [a0, zero_div]; exact Finset.sum_nonneg fun j _ => G0 j 0
    set j := Nat.log 2 n
    have hj1 : 2 ^ j ≤ n := Nat.pow_log_le_self 2 hn0.ne'
    have hj2 : n < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hjN : j < N := by
      have : j < 2 ^ j := Nat.lt_two_pow_self
      have := Finset.mem_range.mp hn
      omega
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => G0 i n) (Finset.mem_range.mpr hjN))
    have npos : (0 : ℝ) < n := by exact_mod_cast hn0
    have h2j : ((2 : ℝ) ^ j) ≤ n := by exact_mod_cast hj1
    have h2j' : (n : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
      have : (n : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hj2
      push_cast at this; rw [pow_succ] at this; linarith
    have P : ((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s ≤ (n : ℝ) ^ k * (n : ℝ) ^ s := by gcongr
    have E : 1 ≤ Real.exp 2 * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹) := by
      rw [← Real.exp_add]; apply Real.one_le_exp
      have : (n : ℝ) * ((2 : ℝ) ^ j)⁻¹ ≤ 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith
      linarith
    have hxj : x ^ j = (((2 : ℝ) ^ j) ^ s)⁻¹ := by
      rw [hxdef, Real.rpow_neg (by norm_num), inv_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
    have L : (n : ℝ) ^ ((k : ℝ) + s) = (n : ℝ) ^ k * (n : ℝ) ^ s := by
      rw [Real.rpow_add npos, Real.rpow_natCast]
    have R : G j n = a n * (Real.exp 2 * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹)) / (((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s) := by
      rw [hG]; dsimp only; rw [hxj]; field_simp
    rw [L, R]
    have an := ha n
    calc a n / ((n : ℝ) ^ k * (n : ℝ) ^ s) ≤ a n / (((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s) := by
          gcongr
      _ ≤ _ := by gcongr; exact le_mul_of_one_le_right an E
  calc ∑ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range N, G j n :=
        Finset.sum_le_sum pt
    _ = ∑ j ∈ Finset.range N, ∑ n ∈ Finset.range N, G j n := Finset.sum_comm
    _ = ∑ j ∈ Finset.range N, Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) *
          ∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹) := by
        simp only [hG, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range N, Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) * (D / (((2 : ℝ) ^ j)⁻¹) ^ k) := by
        gcongr with j _
        exact hD _ (by positivity) N
    _ = ∑ j ∈ Finset.range N, Real.exp 2 * D * x ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [inv_pow]; field_simp
    _ = Real.exp 2 * D * ∑ j ∈ Finset.range N, x ^ j := by rw [Finset.mul_sum]
    _ ≤ Real.exp 2 * D * (x ^ 0 / (1 - x)) := by
        gcongr
        rw [Finset.range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one hx0 hx1
    _ = Real.exp 2 * D / (1 - x) := by rw [pow_zero]; ring

theorem geo (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) : s / 3 ≤ 1 - (2 : ℝ) ^ (-s) := by
  have L := Real.log_two_gt_d9
  have h1 : 1 + s * Real.log 2 ≤ (2 : ℝ) ^ s := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    linarith [Real.add_one_le_exp (Real.log 2 * s)]
  have hp : 0 < 1 + s * Real.log 2 := by nlinarith
  have h2 : (2 : ℝ) ^ (-s) ≤ 1 / (1 + s * Real.log 2) := by
    rw [Real.rpow_neg (by norm_num), one_div]
    exact inv_anti₀ hp h1
  have h3 : 1 / (1 + s * Real.log 2) ≤ 1 - s / 3 := by
    rw [div_le_iff₀ hp]
    have q : 0 ≤ Real.log 2 - 1 / 3 - s * Real.log 2 / 3 := by nlinarith
    nlinarith [mul_nonneg hs.le q]
  linarith

end GlobalTheory.MeanSquareEstimates

namespace GlobalTheory

open GlobalTheory.MeanSquareEstimates in

theorem rankin_mean_square : ∀ (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ), 1 ≤ k → CF k L χ h → h 0 = 0 ∧ (∃ C : ℝ, ∀ n : ℕ, ‖h n‖ ^ 2 ≤ C * (n : ℝ) ^ k) ∧ (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s)) ∧ ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ C := by
  intro k L χ h hk hc
  obtain ⟨C, hC⟩ := hc.2
  have C0 : 0 ≤ C := le_trans (by positivity) (hC UpperHalfPlane.I)
  set D := C * (4 * π) ^ k with hDdef
  have D0 : 0 ≤ D := by positivity
  have K := key2 k L χ h hc C hC
  have K1 : ∀ t : ℝ, 0 < t → ∀ n : ℕ, ‖h n‖ ^ 2 * Real.exp (-(n : ℝ) * t) ≤ D / t ^ k := by
    intro t ht n
    refine le_trans ?_ (K t ht (n + 1))
    exact Finset.single_le_sum (f := fun m : ℕ => ‖h m‖ ^ 2 * Real.exp (-(m : ℝ) * t)) (fun m _ => by positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have h0 : h 0 = 0 := by
    have lim : Tendsto (fun t : ℝ => D / t ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega))
    have b : ‖h 0‖ ^ 2 ≤ 0 := by
      refine ge_of_tendsto lim ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      simpa using K1 t ht 0
    have : ‖h 0‖ = 0 := by nlinarith [norm_nonneg (h 0)]
    exact norm_eq_zero.mp this
  have B : ∀ s : ℝ, 0 < s → ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s)) :=
    fun s hs N => blk (fun n => ‖h n‖ ^ 2) (fun n => by positivity) (by simp [h0]) k D K s hs N
  have nn : ∀ s : ℝ, ∀ n : ℕ, 0 ≤ ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) := fun s n => by positivity
  refine ⟨h0, ⟨D * Real.exp 1, fun n => ?_⟩, fun s hs => summable_of_sum_range_le (nn s) (B s hs), ⟨3 * (Real.exp 2 * D), fun s hs hs1 => ?_⟩⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h0, zero_pow (by omega : k ≠ 0)]
    have npos : (0 : ℝ) < n := by exact_mod_cast hn
    have := K1 (n : ℝ)⁻¹ (by positivity) n
    rw [neg_mul, mul_inv_cancel₀ npos.ne', inv_pow, div_inv_eq_mul] at this
    have e : ‖h n‖ ^ 2 = ‖h n‖ ^ 2 * Real.exp (-1) * Real.exp 1 := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [e]
    calc ‖h n‖ ^ 2 * Real.exp (-1) * Real.exp 1 ≤ D * (n : ℝ) ^ k * Real.exp 1 := by gcongr
      _ = D * Real.exp 1 * (n : ℝ) ^ k := by ring
  · have T := Real.tsum_le_of_sum_range_le (nn s) (B s hs)
    have g := geo s hs hs1
    have pos : 0 < 1 - (2 : ℝ) ^ (-s) := by linarith
    calc s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ s * (Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s))) := by gcongr
      _ ≤ 3 * (Real.exp 2 * D) := by
        rw [mul_div_assoc', div_le_iff₀ pos]
        have : 0 ≤ Real.exp 2 * D := by positivity
        nlinarith

end GlobalTheory
