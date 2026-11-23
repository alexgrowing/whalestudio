import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDefs

open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma mco_one {Y N : ℕ} (hY : 1 ≤ Y) (hN : 1 ≤ N) : mco Y N 1 = 1 := by
  unfold mco
  have h : (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = 1) = {(1, 1)} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_Icc, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha1, -⟩, hb1, -⟩, h⟩
      constructor <;> nlinarith
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨⟨le_rfl, hY⟩, le_rfl, hN⟩, rfl⟩
  rw [h, sum_singleton]
  simp

lemma mco_filter_eq_antidiag {Y N n : ℕ} (hn : 1 ≤ n) (hnY : n ≤ Y) (hYN : Y ≤ N) :
    (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨h, by omega⟩
  · rintro ⟨h, -⟩
    have ha : a ≠ 0 := by
      rintro rfl
      omega
    have hb : b ≠ 0 := by
      rintro rfl
      omega
    have ha' : a ≤ n := Nat.le_of_dvd (by omega) (Dvd.intro b h)
    have hb' : b ≤ n := Nat.le_of_dvd (by omega) (Dvd.intro_left a h)
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, h⟩

lemma mco_filter_subset_antidiag {Y N n : ℕ} (hn : 1 ≤ n) :
    (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) ⊆ n.divisorsAntidiagonal := by
  intro x hx
  rw [mem_filter] at hx
  rw [Nat.mem_divisorsAntidiagonal]
  exact ⟨hx.2, by omega⟩

lemma mco_sum_moebius_divisors {n : ℕ} (hn : 2 ≤ n) : ∑ i ∈ n.divisors, (μ i : ℤ) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply] at h
  rw [h, one_apply_ne (by omega)]

lemma mco_eq_zero {Y N n : ℕ} (h2 : 2 ≤ n) (hnY : n ≤ Y) (hYN : Y ≤ N) : mco Y N n = 0 := by
  unfold mco
  rw [mco_filter_eq_antidiag (by omega) hnY hYN]
  have h := Nat.sum_divisorsAntidiagonal (fun a _ => ((μ a : ℤ) : ℂ)) (n := n)
  rw [h]
  exact_mod_cast mco_sum_moebius_divisors h2

lemma mco_norm_le (Y N : ℕ) {n : ℕ} (hn : 1 ≤ n) : ‖mco Y N n‖ ≤ (n.divisors.card : ℝ) := by
  unfold mco
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (sum_le_sum (g := fun _ => (1 : ℝ)) ?_) ?_
  · intro p _
    have h1 := abs_moebius_le_one (n := p.1)
    first
      | (rw [Complex.norm_intCast]; exact_mod_cast h1)
      | (rw [Complex.norm_int]; exact_mod_cast h1)
      | (rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]; exact_mod_cast h1)
  · rw [sum_const, nsmul_eq_mul, mul_one]
    have hc := card_le_card (mco_filter_subset_antidiag (Y := Y) (N := N) hn)
    have he : n.divisorsAntidiagonal.card = n.divisors.card := by
      first
        | exact Nat.card_divisorsAntidiagonal_eq_card_divisors n
        | (rw [← Nat.map_div_right_divisors, card_map])
    rw [he] at hc
    exact_mod_cast hc

theorem mollifier_identity : MollId := by
  unfold MollId
  intro q _ χ s Y N K hY hYN hK
  have hN : 1 ≤ N := le_trans hY hYN
  have hYK : Y ≤ K := by
    calc Y = Y * 1 := (mul_one Y).symm
      _ ≤ Y * N := Nat.mul_le_mul le_rfl hN
      _ ≤ K := hK
  have hmaps : ∀ p ∈ Icc 1 Y ×ˢ Icc 1 N, p.1 * p.2 ∈ Icc 1 K := by
    intro p hp
    simp only [mem_product, mem_Icc] at hp ⊢
    constructor
    · have := Nat.mul_le_mul hp.1.1 hp.2.1
      simpa using this
    · exact le_trans (Nat.mul_le_mul hp.1.2 hp.2.2) hK
  rw [sum_mul]
  simp_rw [mul_sum]
  rw [sum_comm, ← sum_product',
    ← sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2) (t := Icc 1 K) hmaps]
  calc _ = ∑ k ∈ Icc 1 K, mco Y N k * χ k * (k : ℂ) ^ (-s) := by
        apply sum_congr rfl
        intro k _
        unfold mco
        rw [sum_mul, sum_mul]
        apply sum_congr rfl
        intro p hp
        rw [mem_filter] at hp
        obtain ⟨-, hpk⟩ := hp
        subst hpk
        simp only [Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
        ring
    _ = 1 + ∑ n ∈ Ioc Y K, mco Y N n * χ n * (n : ℂ) ^ (-s) := by
        have hsplit : Icc 1 K = Icc 1 Y ∪ Ioc Y K := by
          ext k
          simp only [mem_union, mem_Icc, mem_Ioc]
          omega
        have hdisj : Disjoint (Icc 1 Y) (Ioc Y K) := by
          rw [disjoint_left]
          intro k hk hk'
          rw [mem_Icc] at hk
          rw [mem_Ioc] at hk'
          omega
        rw [hsplit, sum_union hdisj]
        congr 1
        rw [sum_eq_single 1]
        · rw [mco_one hY hN]
          simp
        · intro k hk hk1
          rw [mem_Icc] at hk
          rw [mco_eq_zero (by omega) hk.2 hYN]
          simp
        · intro h
          exact absurd (mem_Icc.mpr ⟨le_rfl, hY⟩) h

theorem coefficient_square_bound : CoeffSqOf := by
  unfold CoeffSqOf
  intro hD
  unfold CoeffSq
  unfold FX.DivisorBound at hD
  have hs0 : s0 = 399 / 400 := by
    unfold s0
    norm_num
  obtain ⟨C, hC⟩ := hD (1 / 400) (by norm_num)
  have hC1 : 1 ≤ C := by
    have h := hC 1 le_rfl
    simpa using h
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro Y N U hU
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hterm : ∀ n ∈ Ioc U (2 * U),
      (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hUn : (U : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have h1 : ‖mco Y N n‖ ≤ C * (n : ℝ) ^ (1 / 400 : ℝ) := le_trans (mco_norm_le Y N hn1) (hC n hn1)
    have h2 : (n : ℝ) ^ (1 / 400 : ℝ) * (n : ℝ) ^ (-s0) = (n : ℝ) ^ (-(199 / 200 : ℝ)) := by
      rw [← Real.rpow_add hnpos, hs0]
      norm_num
    have h3 : (n : ℝ) ^ (-(199 / 200 : ℝ)) ≤ (U : ℝ) ^ (-(199 / 200 : ℝ)) := by
      first
        | exact Real.rpow_le_rpow_of_nonpos hUpos hUn (by norm_num)
        | exact Real.rpow_le_rpow_of_exponent_nonpos hUpos hUn (by norm_num)
        | (rw [Real.rpow_neg hnpos.le, Real.rpow_neg hUpos.le]
           exact inv_anti₀ (Real.rpow_pos_of_pos hUpos _) (Real.rpow_le_rpow hUpos.le hUn (by norm_num)))
        | (rw [Real.rpow_neg hnpos.le, Real.rpow_neg hUpos.le]
           exact inv_le_inv_of_le (Real.rpow_pos_of_pos hUpos _) (Real.rpow_le_rpow hUpos.le hUn (by norm_num)))
    have h4 : 0 ≤ ‖mco Y N n‖ * (n : ℝ) ^ (-s0) := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hnpos.le _)
    have h5 : ‖mco Y N n‖ * (n : ℝ) ^ (-s0) ≤ C * (U : ℝ) ^ (-(199 / 200 : ℝ)) := by
      calc ‖mco Y N n‖ * (n : ℝ) ^ (-s0) ≤ C * (n : ℝ) ^ (1 / 400 : ℝ) * (n : ℝ) ^ (-s0) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hnpos.le _)
        _ = C * (n : ℝ) ^ (-(199 / 200 : ℝ)) := by rw [mul_assoc, h2]
        _ ≤ C * (U : ℝ) ^ (-(199 / 200 : ℝ)) := mul_le_mul_of_nonneg_left h3 (by linarith)
    first
      | exact pow_le_pow_left h4 h5 2
      | exact pow_le_pow_left₀ h4 h5 2
      | nlinarith
  have e1 : ((U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 = (U : ℝ) ^ (-(199 / 100 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hUpos.le]
    norm_num
  have e2 : (U : ℝ) * (U : ℝ) ^ (-(199 / 100 : ℝ)) = (U : ℝ) ^ (-(99 / 100 : ℝ)) := by
    rw [show (U : ℝ) ^ (-(99 / 100 : ℝ)) = (U : ℝ) ^ ((1 : ℝ) + -(199 / 100 : ℝ)) by norm_num,
      Real.rpow_add hUpos, Real.rpow_one]
  calc ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2
      ≤ ∑ n ∈ Ioc U (2 * U), (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := sum_le_sum hterm
    _ = (U : ℝ) * (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := by
        rw [sum_const, Nat.card_Ioc, show 2 * U - U = U by omega, nsmul_eq_mul]
    _ = C ^ 2 * ((U : ℝ) * ((U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2) := by ring
    _ = C ^ 2 * (U : ℝ) ^ (-(99 / 100 : ℝ)) := by rw [e1, e2]
    _ ≤ C ^ 2 * (U : ℝ) ^ (-(197 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)) (by positivity)

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
