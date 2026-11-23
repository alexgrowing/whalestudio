import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensSt
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZMoll

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma divSq_harm (x : ℕ) : ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ ≤ 1 + Real.log x := by
  have h := harmonic_le_one_add_log x
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

lemma divSq_count (x : ℕ) : ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 =
    ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((x / Nat.lcm p.1 p.2 : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 =
      ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, if Nat.lcm p.1 p.2 ∣ n then (1 : ℝ) else 0 := by
    intro n hn
    rw [mem_Icc] at hn
    have hd : n.divisors = (Icc 1 x).filter (· ∣ n) := by
      ext a
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨h, h0⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), (Nat.le_of_dvd (by omega) h).trans hn.2⟩, h⟩
      · rintro ⟨_, h⟩
        exact ⟨h, by omega⟩
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, sq, ← Nat.cast_mul,
      ← card_product, hd, ← filter_product]
    congr 2
    ext p
    simp [Nat.lcm_dvd_iff]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, ← Nat.Ioc_filter_dvd_card_eq_div]
  rfl

lemma divSq_lcm {a b : ℕ} (ha : 1 ≤ a) :
    Nat.lcm a b = Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have h1 : Nat.gcd a b * (a / Nat.gcd a b) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have h2 : Nat.gcd a b * (b / Nat.gcd a b) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  apply Nat.eq_of_mul_eq_mul_left hg
  calc Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
    _ = (Nat.gcd a b * (a / Nat.gcd a b)) * (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [h1, h2]
    _ = Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b)) := by ring

lemma divSq_cube (x : ℕ) :
    ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ ≤ (∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹) ^ 3 := by
  set φ : ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)
    with hφ
  set F : ℕ × ℕ × ℕ → ℝ := fun t => ((t.1 : ℝ))⁻¹ * (((t.2.1 : ℝ))⁻¹ * ((t.2.2 : ℝ))⁻¹) with hF
  have hinj : Set.InjOn φ (Icc 1 x ×ˢ Icc 1 x : Finset (ℕ × ℕ)) := by
    intro p _ q _ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨hg, h1, h2⟩ := h
    have e1 : Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) = p.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e2 : Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) = p.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have e3 : Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) = q.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e4 : Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) = q.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    ext
    · calc p.1 = Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) := e1.symm
        _ = Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) := by rw [h1, hg]
        _ = q.1 := e3
    · calc p.2 = Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) := e2.symm
        _ = Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) := by rw [h2, hg]
        _ = q.2 := e4
  have hsub : (Icc 1 x ×ˢ Icc 1 x).image φ ⊆ Icc 1 x ×ˢ (Icc 1 x ×ˢ Icc 1 x) := by
    intro t ht
    rw [mem_image] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    simp only [mem_product, mem_Icc] at hp
    obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hp
    have hg : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ a1
    simp only [hφ, mem_product, mem_Icc]
    refine ⟨⟨hg, (Nat.le_of_dvd a1 (Nat.gcd_dvd_left _ _)).trans a2⟩,
      ⟨Nat.div_pos (Nat.le_of_dvd a1 (Nat.gcd_dvd_left _ _)) hg, (Nat.div_le_self _ _).trans a2⟩,
      ⟨Nat.div_pos (Nat.le_of_dvd b1 (Nat.gcd_dvd_right _ _)) hg, (Nat.div_le_self _ _).trans b2⟩⟩
  calc ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹
      = ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, F (φ p) := by
        refine sum_congr rfl fun p hp => ?_
        simp only [mem_product, mem_Icc] at hp
        rw [divSq_lcm hp.1.1]
        simp only [hF, hφ]
        push_cast
        rw [mul_inv, mul_inv, mul_assoc]
    _ = ∑ t ∈ (Icc 1 x ×ˢ Icc 1 x).image φ, F t := (sum_image hinj).symm
    _ ≤ ∑ t ∈ Icc 1 x ×ˢ (Icc 1 x ×ˢ Icc 1 x), F t := by
        refine sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => ?_
        simp only [hF]
        positivity
    _ = (∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹) ^ 3 := by
        simp only [hF]
        rw [sum_product]
        simp only [sum_product, ← mul_sum, ← sum_mul]
        ring

theorem divisor_square_bound : DivSq := by
  intro x hx
  have hlog : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  have hH0 : 0 ≤ ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ := sum_nonneg fun k _ => by positivity
  calc ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2
      = ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((x / Nat.lcm p.1 p.2 : ℕ) : ℝ) := divSq_count x
    _ ≤ ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, (x : ℝ) * ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ := by
        refine sum_le_sum fun p _ => ?_
        rw [← div_eq_mul_inv]
        exact Nat.cast_div_le
    _ = (x : ℝ) * ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ (x : ℝ) * (1 + Real.log x) ^ 3 := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg x)
        exact (divSq_cube x).trans (pow_le_pow_left₀ hH0 (divSq_harm x) 3)

theorem coefficient_block_bound : CoefficientBlockBound := by
  intro Y N U σ hU hσ
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hterm : ∀ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2 ≤
      (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hUn : (U : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have h1 : ‖mco Y N n‖ ≤ (n.divisors.card : ℝ) := mco_norm_le Y N hn1
    have h2 : (n : ℝ) ^ (-σ) ≤ (U : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hU0 hUn (by linarith)
    have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h4 : ((U : ℝ) ^ (-σ)) ^ 2 = (U : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
      congr 1
      push_cast
      ring
    calc (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2
        ≤ ((n.divisors.card : ℝ) * (U : ℝ) ^ (-σ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) h3)
            (mul_le_mul h1 h2 h3 (Nat.cast_nonneg _)) 2
      _ = (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
          rw [mul_pow, h4, mul_comm]
  have hsub : Ioc U (2 * U) ⊆ Icc 1 (2 * U) := by
    intro n hn
    rw [mem_Ioc] at hn
    rw [mem_Icc]
    omega
  have hD := divisor_square_bound (2 * U) (by omega)
  have hpow : (U : ℝ) ^ (1 - 2 * σ) = (U : ℝ) ^ (-(2 * σ)) * U := by
    rw [show (1 - 2 * σ) = -(2 * σ) + 1 by ring, Real.rpow_add hU0, Real.rpow_one]
  calc ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2
      ≤ ∑ n ∈ Ioc U (2 * U), (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := sum_le_sum hterm
    _ = (U : ℝ) ^ (-(2 * σ)) * ∑ n ∈ Ioc U (2 * U), ((n.divisors.card : ℕ) : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ (U : ℝ) ^ (-(2 * σ)) * ∑ n ∈ Icc 1 (2 * U), ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hU0.le _)
        exact sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ ≤ (U : ℝ) ^ (-(2 * σ)) * (((2 * U : ℕ) : ℝ) * (1 + Real.log ((2 * U : ℕ) : ℝ)) ^ 3) :=
        mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hU0.le _)
    _ = 2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 := by
        rw [hpow]
        push_cast
        ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
