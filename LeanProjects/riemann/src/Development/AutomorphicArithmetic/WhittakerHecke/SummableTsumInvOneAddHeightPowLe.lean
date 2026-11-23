import Mathlib

private lemma gen {ι : Type*} (R : Set ι) (f : ι → ℝ) (hf : ∀ x, 0 ≤ f x) (τ : ι → ℤ × ℤ)
    (hinj : Set.InjOn τ R) (w : ℤ × ℤ → ℝ) (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x ∈ R, f x ≤ K * w (τ x)) :
    Summable (R.indicator f) ∧ ∑' x, R.indicator f x ≤ K * ∑' x, w x := by
  classical
  have hinj' : Function.Injective (fun x : R => τ x.1) := by
    intro a b h
    exact Subtype.ext (hinj a.2 b.2 h)
  have hs : Summable (fun x : R => w (τ x.1)) := hw.comp_injective hinj'
  have hs2 : Summable (fun x : R => f x.1) :=
    Summable.of_nonneg_of_le (fun x => hf _) (fun x => hb x.1 x.2) (hs.mul_left K)
  refine ⟨summable_subtype_iff_indicator.mp hs2, ?_⟩
  rw [← tsum_subtype R f]
  calc ∑' x : R, f x.1 ≤ ∑' x : R, K * w (τ x.1) :=
        hs2.tsum_le_tsum (fun x => hb x.1 x.2) (hs.mul_left K)
    _ = K * ∑' x : R, w (τ x.1) := tsum_mul_left
    _ ≤ K * ∑' x, w x := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact Summable.tsum_le_tsum_of_inj _ hinj' (fun c _ => hw0 c) (fun _ => le_rfl) hs hw

private lemma wsum1 : Summable (fun l : ℤ => ((1 + |(l : ℝ)|) ^ 2)⁻¹) := by
  have h0 : Summable (fun m : ℕ => ((1 + (m : ℝ)) ^ 2)⁻¹) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h' := (summable_nat_add_iff 1).mpr h
    refine h'.congr (fun m => ?_)
    push_cast
    rw [one_div, add_comm]
  apply Summable.of_nat_of_neg
  · refine h0.congr (fun m => ?_)
    simp
  · refine h0.congr (fun m => ?_)
    simp

private lemma wsum : Summable (fun p : ℤ × ℤ => ((1 + |(p.1 : ℝ)|) ^ 2)⁻¹ * ((1 + |(p.2 : ℝ)|) ^ 2)⁻¹) :=
  Summable.mul_of_nonneg wsum1 wsum1 (fun _ => by positivity) (fun _ => by positivity)

private lemma round_bd (x : ℝ) : 1 + |((round x : ℤ) : ℝ)| ≤ 2 * (1 + |x|) := by
  have h := abs_sub_round x
  have h2 : |((round x : ℤ) : ℝ)| ≤ |x| + |x - round x| := by
    have := abs_sub_abs_le_abs_sub ((round x : ℤ) : ℝ) x
    rw [abs_sub_comm] at this
    linarith
  linarith [abs_nonneg x]

private lemma nu_lower (κ Bu α T d ν a b : ℝ) (hd : 1 ≤ d) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hBu : 1 ≤ Bu)
    (hα : Bu⁻¹ ≤ α) (hαT : α ≤ T) (hT : 1 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hν : ν = a * α + b / α) :
    (κ / (Bu * d)) * (κ / (T * d)) * ((1 + d * a) * (1 + d * b)) ≤ (1 + κ * ν) ^ 2 := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have hδ : κ / (Bu * d) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hδ' : κ / (T * d) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hA : (κ / (Bu * d)) * (1 + d * a) ≤ 1 + κ * (a * α) := by
    have e : (κ / (Bu * d)) * (1 + d * a) = κ / (Bu * d) + κ * (a * Bu⁻¹) := by
      field_simp
    rw [e]
    have : κ * (a * Bu⁻¹) ≤ κ * (a * α) := by gcongr
    linarith
  have hB : (κ / (T * d)) * (1 + d * b) ≤ 1 + κ * (b / α) := by
    have e : (κ / (T * d)) * (1 + d * b) = κ / (T * d) + κ * (b / T) := by
      field_simp
    rw [e]
    have : κ * (b / T) ≤ κ * (b / α) := by gcongr
    linarith
  have hA0 : 0 ≤ κ * (a * α) := by positivity
  have hB0 : 0 ≤ κ * (b / α) := by positivity
  have hprod : ((κ / (Bu * d)) * (1 + d * a)) * ((κ / (T * d)) * (1 + d * b))
      ≤ (1 + κ * (a * α)) * (1 + κ * (b / α)) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have e2 : (1 + κ * ν) = 1 + κ * (a * α) + κ * (b / α) := by rw [hν]; ring
  rw [e2]
  nlinarith [mul_nonneg hA0 hB0]

private lemma lower_bound_first_case (d Bu T α a b : ℝ) (hd : 1 ≤ d) (hBu : 1 ≤ Bu) (hα : Bu⁻¹ ≤ α) (hT : 1 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 1 ≤ d * a) : 1 / (d * Bu * T) ≤ a * α + b / α := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have h1 : d⁻¹ ≤ a := by
    rw [inv_le_iff_one_le_mul₀ hd0]; linarith
  have h2 : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT
  have h3 : Bu⁻¹ * T⁻¹ ≤ α := by
    have : Bu⁻¹ * T⁻¹ ≤ Bu⁻¹ * 1 := by gcongr
    linarith
  have e : 1 / (d * Bu * T) = d⁻¹ * (Bu⁻¹ * T⁻¹) := by
    field_simp
  rw [e]
  have : d⁻¹ * (Bu⁻¹ * T⁻¹) ≤ a * α := mul_le_mul h1 h3 (by positivity) ha
  have h4 : 0 ≤ b / α := by positivity
  linarith

private lemma lower_bound_second_case (d Bu T α a b : ℝ) (hd : 1 ≤ d) (hBu : 1 ≤ Bu) (hα : Bu⁻¹ ≤ α) (hαT : α ≤ T)
    (hT : 1 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 1 ≤ d * b) : 1 / (d * Bu * T) ≤ a * α + b / α := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have h1 : d⁻¹ ≤ b := by
    rw [inv_le_iff_one_le_mul₀ hd0]; linarith
  have h2 : Bu⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hBu
  have h3 : T⁻¹ ≤ α⁻¹ := inv_anti₀ hα0 hαT
  have h5 : Bu⁻¹ * T⁻¹ ≤ α⁻¹ := by
    have : Bu⁻¹ * T⁻¹ ≤ 1 * T⁻¹ := by gcongr
    linarith
  have e : 1 / (d * Bu * T) = d⁻¹ * (Bu⁻¹ * T⁻¹) := by
    field_simp
  rw [e, div_eq_mul_inv]
  have : d⁻¹ * (Bu⁻¹ * T⁻¹) ≤ b * α⁻¹ := mul_le_mul h1 h5 (by positivity) hb
  have h4 : 0 ≤ a * α := by positivity
  linarith

private lemma term_bd (n : ℕ) (κ Bu α T d ν a b t L M : ℝ) (hd : 1 ≤ d) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hBu : 1 ≤ Bu) (hα : Bu⁻¹ ≤ α) (hαT : α ≤ T) (hT : 1 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 ≤ t) (hν : ν = a * α + b / α) (hν1 : 1 / (d * Bu * T) ≤ ν) (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hL : 1 + L ≤ 2 * (1 + d * a)) (hM : 1 + M ≤ 2 * (1 + d * b)) :
    ((1 + κ * Real.exp t * ν) ^ (n + 4))⁻¹ ≤
      (16 * (d * Bu / κ) ^ n * ((d / κ) * (Bu * d / κ)) ^ 2) * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2) *
        (((1 + L) ^ 2)⁻¹ * ((1 + M) ^ 2)⁻¹) := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hE1 : 1 ≤ Real.exp t := Real.one_le_exp ht
  set E := Real.exp t with hE
  have hE0 : 0 < E := by linarith
  have hlow := nu_lower κ Bu α T d ν a b hd hκ hκ1 hBu hα hαT hT ha hb hν
  set X := 1 + κ * E * ν with hX
  have hX1 : κ * E * (1 / (d * Bu * T)) ≤ X := by
    have : κ * E * (1 / (d * Bu * T)) ≤ κ * E * ν := by gcongr
    have h0 : 0 ≤ κ * E * ν := by positivity
    linarith
  have hX2 : 1 + κ * ν ≤ X := by
    have : κ * ν ≤ κ * E * ν := by
      have : κ * 1 ≤ κ * E := by gcongr
      nlinarith
    linarith
  have hQ : (1 + L) * (1 + M) ≤ 4 * ((1 + d * a) * (1 + d * b)) := by
    have := mul_le_mul hL hM (by positivity) (by positivity)
    nlinarith
  set c1 := κ / (Bu * d) with hc1
  set c2 := κ / (T * d) with hc2
  have hc10 : 0 < c1 := by positivity
  have hc20 : 0 < c2 := by positivity
  have hY : (c1 * c2 / 4) * ((1 + L) * (1 + M)) ≤ (1 + κ * ν) ^ 2 := by
    have h1 : c1 * c2 * ((1 + L) * (1 + M)) ≤ c1 * c2 * (4 * ((1 + d * a) * (1 + d * b))) := by gcongr
    nlinarith
  have hY0 : 0 < (c1 * c2 / 4) * ((1 + L) * (1 + M)) := by positivity
  have hX4 : ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2 ≤ X ^ 4 := by
    calc ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2 ≤ ((1 + κ * ν) ^ 2) ^ 2 := by gcongr
      _ = (1 + κ * ν) ^ 4 := by ring
      _ ≤ X ^ 4 := by
        have : 0 ≤ 1 + κ * ν := by positivity
        gcongr
  have hXn : (κ * E * (1 / (d * Bu * T))) ^ n ≤ X ^ n := by gcongr
  have hmain : (κ * E * (1 / (d * Bu * T))) ^ n * ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2
      ≤ X ^ (n + 4) := by
    rw [pow_add]
    exact mul_le_mul hXn hX4 (by positivity) (by positivity)
  have hpos : 0 < (κ * E * (1 / (d * Bu * T))) ^ n * ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2 := by
    positivity
  refine (inv_anti₀ hpos hmain).trans (le_of_eq ?_)
  have hexp : Real.exp (-((n : ℝ) * t)) = (E ^ n)⁻¹ := by
    rw [Real.exp_neg, Real.exp_nat_mul]
  rw [hexp, hc1, hc2, pow_add T n 2]
  have e1 : κ * E * (1 / (d * Bu * T)) = (κ / (d * Bu)) * E * T⁻¹ := by
    field_simp
  have e2 : d * Bu / κ = (κ / (d * Bu))⁻¹ := by
    rw [inv_div]
  rw [e1, e2, mul_pow, mul_pow, inv_pow, inv_pow]
  have hu : κ / (d * Bu) ≠ 0 := by positivity
  have hun : (κ / (d * Bu)) ^ n ≠ 0 := pow_ne_zero _ hu
  have hEn : E ^ n ≠ 0 := pow_ne_zero _ hE0.ne'
  have hTn : T ^ n ≠ 0 := pow_ne_zero _ hT0.ne'
  generalize (κ / (d * Bu)) ^ n = U at *
  generalize E ^ n = V at *
  generalize T ^ n = W' at *
  have hL1 : 1 + L ≠ 0 := by positivity
  have hM1 : 1 + M ≠ 0 := by positivity
  field_simp
  ring

theorem UpperTheory.summable_tsum_inv_one_add_height_pow_le :
    ∀ (n d : ℕ) (κ Bu : ℝ), 0 < d → 0 < κ → κ ≤ 1 → 1 ≤ Bu → ∃ B : ℝ, 0 ≤ B ∧
        ∀ (R : Set {r : Fin 2 → ℚ // r ≠ 0}) (β α T t : ℝ), 0 ≤ t → Bu⁻¹ ≤ α → α ≤ T → 1 ≤ T →
          (∀ ξ ∈ R, ∃ l : ℤ, (d : ℚ) * ξ.1 0 = l) →
          (∀ ξ ∈ R, ξ.1 0 = 0 → ∃ l : ℤ, (d : ℚ) * ξ.1 1 = l) →
          (∀ ξ ∈ R, ∀ ξ' ∈ R, ξ.1 0 = ξ'.1 0 → ∃ l : ℤ, (d : ℚ) * (ξ.1 1 - ξ'.1 1) = l) →
          Summable (R.indicator fun ξ : {r : Fin 2 → ℚ // r ≠ 0} =>
            ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹) ∧
          ∑' ξ : {r : Fin 2 → ℚ // r ≠ 0}, R.indicator (fun ξ : {r : Fin 2 → ℚ // r ≠ 0} =>
            ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹) ξ
            ≤ B * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2) := by
  intro n d κ Bu hd hκ hκ1 hBu
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hBu0 : 0 < Bu := by linarith
  set w : ℤ × ℤ → ℝ := fun p => ((1 + |(p.1 : ℝ)|) ^ 2)⁻¹ * ((1 + |(p.2 : ℝ)|) ^ 2)⁻¹ with hw
  have hw0 : ∀ p, 0 ≤ w p := fun p => by simp only [hw]; positivity
  set C : ℝ := 16 * ((d : ℝ) * Bu / κ) ^ n * (((d : ℝ) / κ) * (Bu * (d : ℝ) / κ)) ^ 2 with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C * ∑' p, w p, mul_nonneg hC0 (tsum_nonneg hw0), ?_⟩
  intro R β α T t ht hα hαT hT h1 h2 h3
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  set τ : {r : Fin 2 → ℚ // r ≠ 0} → ℤ × ℤ := fun ξ =>
    (round ((d : ℝ) * ((ξ.1 0 : ℚ) : ℝ)),
      round ((d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)))) with hτ
  have hinj : Set.InjOn τ R := by
    intro ξ hξ ξ' hξ' he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    simp only [hτ] at he1 he2
    obtain ⟨l, hl⟩ := h1 ξ hξ
    obtain ⟨l', hl'⟩ := h1 ξ' hξ'
    have hlR : (d : ℝ) * ((ξ.1 0 : ℚ) : ℝ) = (l : ℝ) := by exact_mod_cast hl
    have hlR' : (d : ℝ) * ((ξ'.1 0 : ℚ) : ℝ) = (l' : ℝ) := by exact_mod_cast hl'
    rw [hlR, hlR', round_intCast, round_intCast] at he1
    have h0 : ξ.1 0 = ξ'.1 0 := by
      have : (d : ℚ) * ξ.1 0 = (d : ℚ) * ξ'.1 0 := by rw [hl, hl', he1]
      exact mul_left_cancel₀ (by exact_mod_cast hd.ne') this
    obtain ⟨j, hj⟩ := h3 ξ hξ ξ' hξ' h0
    have hjR : (d : ℝ) * (((ξ.1 1 : ℚ) : ℝ) - ((ξ'.1 1 : ℚ) : ℝ)) = (j : ℝ) := by exact_mod_cast hj
    have e : (d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ))
        = (d : ℝ) * (((ξ'.1 0 : ℚ) : ℝ) * β + ((ξ'.1 1 : ℚ) : ℝ)) + (j : ℝ) := by
      rw [← hjR, h0]; ring
    rw [e, round_add_intCast] at he2
    have hj0 : j = 0 := by linarith
    have h1' : ξ.1 1 = ξ'.1 1 := by
      rw [hj0] at hj
      have : (d : ℚ) * (ξ.1 1 - ξ'.1 1) = 0 := by simpa using hj
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by exact_mod_cast hd.ne')
      · exact sub_eq_zero.mp h
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h0
    · exact h1'
  have hb : ∀ ξ ∈ R, ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹
      ≤ (C * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2)) * w (τ ξ) := by
    intro ξ hξ
    have hν1 : 1 / ((d : ℝ) * Bu * T) ≤ |((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α := by
      by_cases hz : ξ.1 0 = 0
      · obtain ⟨l, hl⟩ := h2 ξ hξ hz
        have hlR : (d : ℝ) * ((ξ.1 1 : ℚ) : ℝ) = (l : ℝ) := by exact_mod_cast hl
        have hne : ξ.1 1 ≠ 0 := by
          intro h
          apply ξ.2
          funext i
          fin_cases i
          · exact hz
          · exact h
        have hl0 : l ≠ 0 := by
          intro h
          rw [h] at hl
          have : (d : ℚ) * ξ.1 1 = 0 := by simpa using hl
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h (by exact_mod_cast hd.ne')
          · exact hne h
        have hl1 : (1 : ℝ) ≤ |(l : ℝ)| := by
          have : (1 : ℤ) ≤ |l| := Int.one_le_abs hl0
          exact_mod_cast this
        apply lower_bound_second_case _ _ _ _ _ _ hd1 hBu hα hαT hT (abs_nonneg _) (abs_nonneg _)
        have hz' : ((ξ.1 0 : ℚ) : ℝ) = 0 := by rw [hz]; simp
        rw [hz', zero_mul, zero_add]
        calc (1 : ℝ) ≤ |(l : ℝ)| := hl1
          _ = (d : ℝ) * |((ξ.1 1 : ℚ) : ℝ)| := by
            rw [← hlR, abs_mul, abs_of_pos hd0]
      · obtain ⟨l, hl⟩ := h1 ξ hξ
        have hlR : (d : ℝ) * ((ξ.1 0 : ℚ) : ℝ) = (l : ℝ) := by exact_mod_cast hl
        have hl0 : l ≠ 0 := by
          intro h
          rw [h] at hl
          have : (d : ℚ) * ξ.1 0 = 0 := by simpa using hl
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h (by exact_mod_cast hd.ne')
          · exact hz h
        have hl1 : (1 : ℝ) ≤ |(l : ℝ)| := by
          have : (1 : ℤ) ≤ |l| := Int.one_le_abs hl0
          exact_mod_cast this
        apply lower_bound_first_case _ _ _ _ _ _ hd1 hBu hα hT (abs_nonneg _) (abs_nonneg _)
        calc (1 : ℝ) ≤ |(l : ℝ)| := hl1
          _ = (d : ℝ) * |((ξ.1 0 : ℚ) : ℝ)| := by
            rw [← hlR, abs_mul, abs_of_pos hd0]
    have hL := round_bd ((d : ℝ) * ((ξ.1 0 : ℚ) : ℝ))
    have hM := round_bd ((d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)))
    rw [abs_mul, abs_of_pos hd0] at hL hM
    exact term_bd n κ Bu α T (d : ℝ) _ _ _ t _ _ hd1 hκ hκ1 hBu hα hαT hT (abs_nonneg _)
      (abs_nonneg _) ht rfl hν1 (abs_nonneg _) (abs_nonneg _) hL hM
  have hf : ∀ ξ : {r : Fin 2 → ℚ // r ≠ 0}, 0 ≤ ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹ := by
    intro ξ
    positivity
  obtain ⟨hs, hle⟩ := gen R _ hf τ hinj w wsum hw0 (C * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2))
    (by positivity) hb
  refine ⟨hs, hle.trans (le_of_eq ?_)⟩
  ring
