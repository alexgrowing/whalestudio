import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimePowerVonMangoldtSumBound

open Finset ArithmeticFunction

namespace GlobalTheory

theorem sum_von_mangoldt_div_sq_Ioc_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (K : ℕ) (hK : 1 ≤ K) (M : ℕ) (hM : K ≤ M) :
    ∑ m ∈ Ioc K M, Λ m / (m : ℝ) ^ 2 ≤
      (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 + 4 / (K : ℝ) - 4 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have : 0 ≤ (∑ n ∈ Icc 1 K, Λ n) / (K : ℝ) ^ 2 :=
      div_nonneg (sum_nonneg fun _ _ => vonMangoldt_nonneg) (sq_nonneg _)
    simp only [Ioc_self, sum_empty]
    linarith
  | succ M hM ih =>
    rw [sum_Ioc_succ_top hM, sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hψ := h M
    set ψ := ∑ n ∈ Icc 1 M, Λ n
    push_cast
    have key : ψ / (M : ℝ) ^ 2 - ψ / ((M : ℝ) + 1) ^ 2 ≤ 4 / (M : ℝ) - 4 / ((M : ℝ) + 1) := by
      have e1 : ψ / (M : ℝ) ^ 2 - ψ / ((M : ℝ) + 1) ^ 2
          = ψ * ((2 * M + 1) / ((M : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)) := by
        field_simp; ring
      have e2 : 4 / (M : ℝ) - 4 / ((M : ℝ) + 1)
          = 2 * M * ((2 * M + 2) / ((M : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)) := by
        field_simp; ring
      rw [e1, e2]
      apply mul_le_mul hψ _ (by positivity) (by positivity)
      gcongr
      norm_num
    rw [add_div]
    linarith

theorem sum_vonMangoldt_div_sq_Ioc_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ m ∈ Ioc K M, Λ m / (m : ℝ) ^ 2 ≤ 4 / (K : ℝ) := by
  rcases le_total K M with hM | hM
  · have h1 := sum_von_mangoldt_div_sq_Ioc_le h K hK M hM
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have h2 : (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 ≤ 4 / (M : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hM0]
      have := h M
      nlinarith
    linarith
  · rw [Ioc_eq_empty (by omega), sum_empty]
    positivity

theorem sum_cn_isSquare_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (x : ℝ) (hx : 1 ≤ x) (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (fun n => IsSquare n), Formalism.HermitianLattices.GL2PrimeSums.cn x n ≤ 10 * Real.sqrt x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hcn : ∀ n : ℕ, 0 ≤ Formalism.HermitianLattices.GL2PrimeSums.cn x n := fun n =>
    mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (div_nonneg hx0 (Nat.cast_nonneg _)))
  set y := Real.sqrt x with hy
  have hy1 : 1 ≤ y := Real.one_le_sqrt.mpr hx
  have hyy : y * y = x := Real.mul_self_sqrt hx0
  set K : ℕ := ⌊y⌋₊ with hKdef
  have hK1 : 1 ≤ K := Nat.le_floor (by simpa using hy1)
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKy : (K : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyK : y < K + 1 := Nat.lt_floor_add_one y
  have hsub : (Icc 1 N).filter (fun n => IsSquare n) ⊆ (Icc 1 K ∪ Ioc K N).image (fun m => m ^ 2) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, r, rfl⟩ := hn
    refine mem_image.mpr ⟨r, ?_, sq r⟩
    have hr : 1 ≤ r := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    have hrN : r ≤ N := le_trans (Nat.le_mul_self r) h2
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 K) (Ioc K N) := by
    rw [disjoint_left]
    intro a h1 h2
    simp only [mem_Icc, mem_Ioc] at h1 h2
    omega
  have hA : ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ 2 * y := by
    calc ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ ∑ m ∈ Icc 1 K, Λ m := by
          refine sum_le_sum fun m _ => ?_
          unfold Formalism.HermitianLattices.GL2PrimeSums.cn
          rw [vonMangoldt_apply_pow (by norm_num)]
          exact mul_le_of_le_one_right vonMangoldt_nonneg (min_le_left _ _)
      _ ≤ 2 * (K : ℝ) := h K
      _ ≤ 2 * y := by linarith
  have hB : ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ 8 * y := by
    calc ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ ∑ m ∈ Ioc K N, x * (Λ m / (m : ℝ) ^ 2) := by
          refine sum_le_sum fun m _ => ?_
          unfold Formalism.HermitianLattices.GL2PrimeSums.cn
          rw [vonMangoldt_apply_pow (by norm_num)]
          calc Λ m * min 1 (x / ((m ^ 2 : ℕ) : ℝ)) ≤ Λ m * (x / ((m ^ 2 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) vonMangoldt_nonneg
            _ = x * (Λ m / (m : ℝ) ^ 2) := by push_cast; ring
      _ = x * ∑ m ∈ Ioc K N, Λ m / (m : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ x * (4 / (K : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_vonMangoldt_div_sq_Ioc_le h K hK1 N) hx0
      _ ≤ 8 * y := by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith), ← hyy]
          nlinarith
  calc ∑ n ∈ (Icc 1 N).filter (fun n => IsSquare n), Formalism.HermitianLattices.GL2PrimeSums.cn x n
      ≤ ∑ n ∈ (Icc 1 K ∪ Ioc K N).image (fun m => m ^ 2), Formalism.HermitianLattices.GL2PrimeSums.cn x n :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hcn n
    _ = ∑ m ∈ Icc 1 K ∪ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) :=
        sum_image fun a _ b _ hab => Nat.pow_left_injective (by norm_num : 2 ≠ 0) hab
    _ = ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) + ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) :=
        sum_union hdisj
    _ ≤ 10 * y := by linarith

theorem remainder_smooth_rough_bound : Formalism.HermitianLattices.GL2a2.SizeR := by
  intro hψ
  have h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ) := fun M => by
    simpa using hψ M (Nat.cast_nonneg M)
  obtain ⟨C, hC⟩ := prime_power_von_mangoldt_sum_bound
  refine ⟨max C 10, fun ε hε _ x hx m₀ hm₀ hp => ?_⟩
  unfold Formalism.HermitianLattices.GL2a2.Rsum
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h10 : (10 : ℝ) ≤ max C 10 := le_max_right _ _
  have hw : 0 ≤ x ^ (ε / 5) := Real.rpow_nonneg hx0.le _
  have h1 := sum_cn_isSquare_le h x (by linarith) ⌊x ^ (400 : ℝ)⌋₊
  rw [Real.sqrt_eq_rpow] at h1
  have hs : 0 ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
  set S := m₀.primeFactors.filter (fun p => p ≤ ⌊x ^ (400 : ℝ)⌋₊) with hS
  have hsub : S ⊆ Icc 1 ⌊x ^ (ε / 5)⌋₊ := by
    intro p hpS
    simp only [hS, mem_filter, Nat.mem_primeFactors] at hpS
    obtain ⟨⟨hpp, hd, _⟩, hle⟩ := hpS
    refine mem_Icc.mpr ⟨hpp.one_le, Nat.le_floor ?_⟩
    rcases hp p hpp hd with h' | h'
    · exact h'
    · exfalso
      have : (p : ℝ) ≤ x ^ (400 : ℝ) :=
        (Nat.le_floor_iff (Real.rpow_nonneg hx0.le _)).mp hle
      linarith
  have hcard : (S.card : ℝ) ≤ x ^ (ε / 5) := by
    have := card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact le_trans (by exact_mod_cast this) (Nat.floor_le hw)
  have h2 : ∑ p ∈ S, Formalism.HermitianLattices.GL2a2.sP x p ≤ max C 10 * (x ^ (ε / 5) * Real.log x) := by
    calc ∑ p ∈ S, Formalism.HermitianLattices.GL2a2.sP x p ≤ S.card • (max C 10 * Real.log x) := by
          refine sum_le_card_nsmul _ _ _ fun p hpS => ?_
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hpS).1
          exact (hC x hx p hpp).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
      _ = (S.card : ℝ) * (max C 10 * Real.log x) := nsmul_eq_mul _ _
      _ ≤ x ^ (ε / 5) * (max C 10 * Real.log x) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg (by linarith) hlog)
      _ = max C 10 * (x ^ (ε / 5) * Real.log x) := by ring
  have h3 : 10 * x ^ ((1 : ℝ) / 2) ≤ max C 10 * x ^ ((1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right h10 hs
  rw [mul_add]
  linarith

end GlobalTheory
