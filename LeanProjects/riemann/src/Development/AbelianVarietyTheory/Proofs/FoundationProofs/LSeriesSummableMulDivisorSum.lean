import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableCardDivisorsSqDivOneAddRpow
open Complex Filter Topology

namespace GlobalTheory.DivConvSum

theorem norm_divisorSum_le (k n : ℕ) (ψ θ : ℕ → ℂ) (h : ∀ n, ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) :
    ‖∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ k * θ p.2‖
      ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ k := by
  have hc : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  refine (norm_sum_le _ _).trans ?_
  rw [← hc, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
  have hle : p.1 ≤ n := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
  have hle' : (p.1 : ℝ) ^ k ≤ (n : ℝ) ^ k :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) k
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  have h1 := (h p.1).1
  have h2 := (h p.2).2
  have h0 : (0 : ℝ) ≤ (p.1 : ℝ) ^ k := by positivity
  calc ‖ψ p.1‖ * (p.1 : ℝ) ^ k * ‖θ p.2‖ ≤ 1 * (p.1 : ℝ) ^ k * 1 := by
        gcongr
    _ ≤ (n : ℝ) ^ k := by simpa using hle'

theorem lSeriesSummable_mul_divisorSum :
    ∀ (e : ℕ) (ψ θ g b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n : ℕ => g n * b n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  intro e ψ θ g b s he hs hψ hg hb
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have h1 := hg s hs
  have h2 := GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow s hs
  refine Summable.of_norm_bounded (h1.add h2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hbn : ‖b n‖ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ k := by
      rw [hb n hn, Nat.add_sub_cancel]
      exact norm_divisorSum_le k n ψ θ hψ
    have e1 : (n : ℝ) ^ (2 * ((k + 1 : ℕ) : ℝ) + s)
        = ((n : ℝ) ^ k * n) ^ 2 * (n : ℝ) ^ s := by
      rw [Real.rpow_add hN, show (2 * ((k + 1 : ℕ) : ℝ)) = ((2 * (k + 1) : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
      ring
    have e2 : (n : ℝ) ^ (((2 * (k + 1) + 1 : ℕ) : ℝ) + s)
        = ((n : ℝ) ^ k * n) ^ 2 * (n * (n : ℝ) ^ s) := by
      rw [Real.rpow_add hN, Real.rpow_natCast]
      ring
    have e3 : (n : ℝ) ^ (1 + s) = n * (n : ℝ) ^ s := by
      rw [Real.rpow_add hN, Real.rpow_one]
    rw [Complex.ofReal_re, norm_mul, e1, e2, e3]
    have hu : (0 : ℝ) < (n : ℝ) ^ s := Real.rpow_pos_of_pos hN s
    have hP : (0 : ℝ) < (n : ℝ) ^ k := by positivity
    generalize (n : ℝ) ^ s = u at *
    generalize (n : ℝ) ^ k = P at *
    generalize (n.divisors.card : ℝ) = d at *
    have hG : 0 ≤ ‖g n‖ := norm_nonneg _
    generalize ‖g n‖ = G at *
    generalize (n : ℝ) = N at *
    calc G * ‖b n‖ / ((P * N) ^ 2 * u) ≤ G * (d * P) / ((P * N) ^ 2 * u) := by gcongr
      _ = (G / (P * N) * d) / (N * u) := by field_simp
      _ ≤ ((G / (P * N)) ^ 2 + d ^ 2) / (N * u) := by
          gcongr
          nlinarith [sq_nonneg (G / (P * N) - d), sq_nonneg (G / (P * N)), sq_nonneg d]
      _ = G ^ 2 / ((P * N) ^ 2 * (N * u)) + d ^ 2 / (N * u) := by field_simp

end GlobalTheory.DivConvSum
