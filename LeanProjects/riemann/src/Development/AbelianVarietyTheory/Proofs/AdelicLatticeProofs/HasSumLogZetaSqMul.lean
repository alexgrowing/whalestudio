import Mathlib

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.LogEulerSeries

theorem hasSum_neg_log_succ {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1)) (-Complex.log (1 - z)) := by
  have h := Complex.hasSum_taylorSeries_neg_log hz
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simpa using h2

theorem hasSum_prod_neg_log {ι : Type} (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1 / 2)
    (hs : Summable fun i => ‖z i‖) :
    HasSum (fun p : ι × ℕ => z p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1))
      (∑' i, -Complex.log (1 - z i)) := by
  have hsum : Summable (fun p : ι × ℕ => z p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1)) := by
    have hb : Summable (fun p : ι × ℕ => ‖z p.1‖ * ((1 / 2 : ℝ) ^ p.2)) :=
      hs.mul_of_nonneg summable_geometric_two (fun i => norm_nonneg _) (fun k => by positivity)
    refine Summable.of_norm_bounded hb ?_
    rintro ⟨i, k⟩
    simp only
    have h1 : (1 : ℝ) ≤ ‖(k : ℂ) + 1‖ := by
      have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]
      exact_mod_cast Nat.le_add_left 1 k
    rw [norm_div, norm_pow, pow_succ, mul_comm]
    calc ‖z i‖ * ‖z i‖ ^ k / ‖(k : ℂ) + 1‖ ≤ ‖z i‖ * ‖z i‖ ^ k := div_le_self (by positivity) h1
      _ ≤ ‖z i‖ * (1 / 2 : ℝ) ^ k := by gcongr; exact hz i
  have hf : ∀ i, HasSum (fun k : ℕ => z i ^ (k + 1) / ((k : ℂ) + 1)) (-Complex.log (1 - z i)) :=
    fun i => hasSum_neg_log_succ (by linarith [hz i])
  have h3 := hsum.hasSum.prod_fiberwise hf
  rw [h3.tsum_eq]
  exact hsum.hasSum

theorem hasSum_one {ι : Type} (N : ι → ℕ) (c : ι → ℂ) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) (hsum : Summable fun i => (N i : ℝ) ^ (-s.re)) :
    HasSum (fun p : ι × ℕ => c p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1) *
        Complex.exp (-((((p.2 : ℝ) + 1) * Real.log (N p.1) : ℝ) : ℂ) * s))
      (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) := by
  have hpos : ∀ i, 0 < N i := fun i => by have := hN i; omega
  have hn : ∀ i, ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ (N i : ℝ) ^ (-s.re) := fun i => by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hpos i), Complex.neg_re]
    exact mul_le_of_le_one_left (by positivity) (hc i)
  have h := hasSum_prod_neg_log (fun i => c i * ((N i : ℕ) : ℂ) ^ (-s)) (fun i => by
    refine (hn i).trans ?_
    have h2 : (2 : ℝ) ≤ N i := by exact_mod_cast hN i
    calc (N i : ℝ) ^ (-s.re) ≤ (N i : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / (N i : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2)
    (Summable.of_nonneg_of_le (fun i => norm_nonneg _) hn hsum)
  convert h using 2 with p
  obtain ⟨i, k⟩ := p
  have hne : ((N i : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (hpos i).ne'
  simp only
  rw [mul_pow, Complex.cpow_def_of_ne_zero hne, ← Complex.exp_nat_mul, ← Complex.natCast_log]
  push_cast
  rw [show ((k : ℂ) + 1) * (Complex.log (N i) * -s) = -(((k : ℂ) + 1) * Complex.log (N i)) * s by ring]
  ring

theorem hasSum_log_zeta_sq_mul : ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → ∀ s : ℂ, 1 < s.re → HasSum (fun p : ι × ℕ => (((2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1) : ℝ) : ℂ) * Complex.exp (-((((p.2 : ℝ) + 1) * Real.log (N p.1) : ℝ) : ℂ) * s)) (2 * (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s))) + (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) + (∑' i, -Complex.log (1 - starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s)))) := by
  intro ι N c hN hc hsum s hs
  have h1 := hasSum_one N (fun _ => 1) hN (fun _ => by simp) s hs (hsum _ hs)
  have h2 := hasSum_one N c hN hc s hs (hsum _ hs)
  have h3 := hasSum_one N (fun i => starRingEnd ℂ (c i)) hN (fun i => by simpa using hc i) s hs
    (hsum _ hs)
  have h := ((h1.mul_left 2).add h2).add h3
  convert h using 1
  · rfl
  funext p
  revert p
  rintro ⟨i, k⟩
  simp only
  generalize Complex.exp _ = E
  rw [← map_pow]
  have := Complex.add_conj (c i ^ (k + 1))
  rw [Complex.ofReal_div, Complex.ofReal_add, ← this]
  push_cast
  ring

end GlobalTheory.LogEulerSeries
