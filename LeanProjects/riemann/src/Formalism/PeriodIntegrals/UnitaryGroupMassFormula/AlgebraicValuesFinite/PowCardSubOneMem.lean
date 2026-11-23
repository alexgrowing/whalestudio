import Mathlib

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem val_alg (y : L) : Valued.v (algebraMap L (v.adicCompletion L) y) = v.valuation L y := by
  exact valuedAdicCompletion_eq_valuation' v y

theorem val_pow_sub_le {x b : v.adicCompletion L} (hx : Valued.v x ≤ 1) (hb : Valued.v b ≤ 1) (k : ℕ) :
    Valued.v (x ^ k - b ^ k) ≤ Valued.v (x - b) := by
  have key : x ^ k - b ^ k = (∑ i ∈ Finset.range k, x ^ i * b ^ (k - 1 - i)) * (x - b) :=
    (geom_sum₂_mul x b k).symm
  rw [key, map_mul]
  have hs : Valued.v (∑ i ∈ Finset.range k, x ^ i * b ^ (k - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one₀ zero_le' hx) (pow_le_one₀ zero_le' hb)
  exact mul_le_of_le_one_left' hs

theorem pow_card_sub_one_mem (n : ℕ) (b : 𝓞 L) (hb : b ∉ v.asIdeal) :
    b ^ Nat.card ((𝓞 L ⧸ v.asIdeal ^ n)ˣ) - 1 ∈ v.asIdeal ^ n := by
  obtain ⟨y, i, hi, hyi⟩ := v.isMaximal.exists_inv hb
  have h1 : (y * ∑ k ∈ Finset.range n, i ^ k) * b = 1 - i ^ n := by
    have hyb : y * b = 1 - i := by linear_combination hyi
    calc (y * ∑ k ∈ Finset.range n, i ^ k) * b = (y * b) * ∑ k ∈ Finset.range n, i ^ k := by ring
      _ = (1 - i) * ∑ k ∈ Finset.range n, i ^ k := by rw [hyb]
      _ = 1 - i ^ n := mul_neg_geom_sum i n
  have hcb : Ideal.Quotient.mk (v.asIdeal ^ n) (y * ∑ k ∈ Finset.range n, i ^ k) *
      Ideal.Quotient.mk (v.asIdeal ^ n) b = 1 := by
    rw [← map_mul, h1, map_sub, map_one,
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.pow_mem_pow hi n), sub_zero]
  let u : (𝓞 L ⧸ v.asIdeal ^ n)ˣ := ⟨Ideal.Quotient.mk _ b, Ideal.Quotient.mk _ (y * ∑ k ∈ Finset.range n, i ^ k),
    by rw [mul_comm]; exact hcb, hcb⟩
  have hu : u ^ Nat.card ((𝓞 L ⧸ v.asIdeal ^ n)ˣ) = 1 := pow_card_eq_one'
  have h2 := congrArg Units.val hu
  rw [Units.val_pow_eq_pow_val, Units.val_one] at h2
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one]
  exact sub_eq_zero.mpr h2

theorem card_units_pos (n : ℕ) : 0 < Nat.card ((𝓞 L ⧸ v.asIdeal ^ n)ˣ) := by
  haveI : Finite (𝓞 L ⧸ v.asIdeal ^ n) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero n v.ne_bot)
  exact Nat.card_pos

theorem exists_pow_close (n : ℕ) : ∃ N : ℕ, 0 < N ∧ ∀ x : v.adicCompletion L, Valued.v x = 1 →
    Valued.v (x ^ N - 1) ≤ exp (-(n : ℤ)) := by
  classical
  refine ⟨Nat.card ((𝓞 L ⧸ v.asIdeal ^ n)ˣ), card_units_pos v n, ?_⟩
  intro x hx
  set N := Nat.card ((𝓞 L ⧸ v.asIdeal ^ n)ˣ) with hN
  have hlt1 : (exp (-((n : ℤ) + 1)) : ℤᵐ⁰) < exp (-(n : ℤ)) := by
    rw [exp_lt_exp]
    omega
  have hle1 : (exp (-(n : ℤ)) : ℤᵐ⁰) ≤ 1 := by
    rw [← exp_zero, exp_le_exp]
    omega
  obtain ⟨y, hy⟩ : ∃ y : L, algebraMap L (v.adicCompletion L) y ∈
      {z : v.adicCompletion L | Valued.v (z - x) < exp (-((n : ℤ) + 1))} := by
    obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
    set w : v.adicCompletion L := algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L π) ^ (n + 1)
      with hw_def
    have hw : Valued.v w = exp (-((n : ℤ) + 1)) := by
      rw [hw_def, map_pow, val_alg, valuation_of_algebraMap, hπ, ← WithZero.exp_nsmul]
      congr 1
      push_cast
      ring
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hw
      exact exp_ne_zero hw.symm
    have hnhds : {z : v.adicCompletion L | Valued.v (z - x) < exp (-((n : ℤ) + 1))} ∈ nhds x := by
      refine Valued.mem_nhds.2 ⟨Units.mk0 (Valued.v.restrict w) ((Valuation.ne_zero_iff _).2 hw0),
        fun z hz => ?_⟩
      simp only [Set.mem_setOf_eq, Units.val_mk0] at hz ⊢
      rw [← hw]
      exact (Valuation.restrict_lt_iff _).1 hz
    exact (denseRange_algebraMap L v).mem_nhds hnhds
  simp only [Set.mem_setOf_eq] at hy
  have hy1 : v.valuation L y ≤ 1 := by
    rw [← val_alg]
    calc Valued.v (algebraMap L (v.adicCompletion L) y)
        = Valued.v ((algebraMap L (v.adicCompletion L) y - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap L (v.adicCompletion L) y - x)) (Valued.v x) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := max_le (le_trans hy.le (le_trans hlt1.le hle1)) hx.le
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (K := L) y
  have hs0 : algebraMap (𝓞 L) L s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 (nonZeroDivisors.ne_zero hs)
  have hsv : v.intValuation s ≠ 0 := by
    rw [← valuation_of_algebraMap (K := L)]
    exact (Valuation.ne_zero_iff _).2 hs0
  have has : v.intValuation a ≤ v.intValuation s := by
    rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
      div_le_one₀ (zero_lt_iff.2 hsv)] at hy1
    exact hy1
  obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.1 hsv
  obtain ⟨t, ht⟩ := v.exists_intValuation_mul_sub_lt has (Multiplicative.ofAdd (-((n : ℤ) + 1)) * g)
  have hyt : Valued.v (algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L s) -
      algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L t)) < exp (-((n : ℤ) + 1)) := by
    rw [← map_sub, val_alg]
    have e : algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L s - algebraMap (𝓞 L) L t =
        algebraMap (𝓞 L) L (a - t * s) / algebraMap (𝓞 L) L s := by
      rw [map_sub, map_mul, sub_div, mul_div_assoc, div_self hs0, mul_one]
    rw [e, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
      div_lt_iff₀ (zero_lt_iff.2 hsv), ← hg]
    calc v.intValuation (a - t * s) < ((Multiplicative.ofAdd (-((n : ℤ) + 1)) * g : Multiplicative ℤ) : ℤᵐ⁰) := ht
      _ = exp (-((n : ℤ) + 1)) * (g : ℤᵐ⁰) := by rw [WithZero.coe_mul]; rfl
  set B := algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L t) with hB
  set Y := algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L a / algebraMap (𝓞 L) L s) with hY
  have hxb : Valued.v (x - B) < exp (-((n : ℤ) + 1)) := by
    have e : x - B = -(Y - x) + (Y - B) := by ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (by rwa [Valuation.map_neg]) hyt)
  have hb1 : Valued.v B ≤ 1 := by
    rw [hB, val_alg, valuation_of_algebraMap]
    exact v.intValuation_le_one t
  have hbP : t ∉ v.asIdeal := by
    intro hmem
    have h1 : v.intValuation t ≤ exp (-((1 : ℕ) : ℤ)) := by
      rw [intValuation_le_pow_iff_mem, pow_one]
      exact hmem
    have h1' : Valued.v B < 1 := by
      rw [hB, val_alg, valuation_of_algebraMap]
      refine lt_of_le_of_lt h1 ?_
      rw [← exp_zero, exp_lt_exp]
      omega
    have h2 : Valued.v (x - B) < 1 := lt_of_lt_of_le hxb (le_trans hlt1.le hle1)
    have h3 : Valued.v x < 1 := by
      have e : x = (x - B) + B := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h2 h1')
    rw [hx] at h3
    exact lt_irrefl _ h3
  have hpow := pow_card_sub_one_mem v n t hbP
  have h2 : Valued.v (B ^ N - 1) ≤ exp (-(n : ℤ)) := by
    rw [hB, ← map_pow, ← map_pow, ← map_one (algebraMap L (v.adicCompletion L)), ← map_sub, val_alg,
      ← map_one (algebraMap (𝓞 L) L), ← map_sub, valuation_of_algebraMap, intValuation_le_pow_iff_mem]
    exact hpow
  have h1 : Valued.v (x ^ N - B ^ N) ≤ exp (-(n : ℤ)) :=
    le_trans (val_pow_sub_le v hx.le hb1 N) (le_trans hxb.le hlt1.le)
  calc Valued.v (x ^ N - 1) = Valued.v ((x ^ N - B ^ N) + (B ^ N - 1)) := by
        rw [sub_add_sub_cancel]
    _ ≤ max (Valued.v (x ^ N - B ^ N)) (Valued.v (B ^ N - 1)) := Valuation.map_add _ _ _
    _ ≤ exp (-(n : ℤ)) := max_le h1 h2

end PI.AlgValsFin.W
