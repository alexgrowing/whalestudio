import Formalism.IncomingBounds.LemmaMNumerics

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

theorem sqSubOneInvMulDvd : InvWeight := by
  intro l hl n n' hdvd
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨m, ?_⟩
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < l - 1).ne'
  have h3 : (l : ℝ) + 1 ≠ 0 := (by linarith : (0 : ℝ) < l + 1).ne'
  have hmR : (n : ℝ) - l * n' = ((l : ℝ) ^ 2 - 1) * m := by exact_mod_cast hm
  have hn : (n : ℝ) = ((l : ℝ) - 1) * ((l : ℝ) + 1) * m + l * n' := by linear_combination hmR
  unfold rho
  rw [hn, show (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) by ring]
  field_simp
  ring

private lemma binomGcd_lucas_lemma (l : ℕ) [Fact l.Prime] (m v : ℕ) :
    (l ^ v * m).choose (l ^ v) ≡ m [MOD l] := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  induction v with
  | zero => simp <;> exact Nat.ModEq.refl _
  | succ v ih =>
    rw [show l ^ (v + 1) * m = l * (l ^ v * m) by ring, show l ^ (v + 1) = l * l ^ v by ring]
    refine Choose.choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
    simp only [Nat.mul_mod_right, Nat.mul_div_cancel_left _ hl, Nat.choose_self, one_mul]
    exact ih

private lemma binomGcd_lucas_lemma_2 (l : ℕ) [Fact l.Prime] (a : ℕ) :
    (l ^ (a + 1) - 1).choose (l ^ a - 1) ≡ 1 [MOD l] := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl0 : 0 < l := by omega
  have hlt : l - 1 < l := by omega
  induction a with
  | zero => simp <;> exact Nat.ModEq.refl _
  | succ a ih =>
    have e1 : 1 ≤ l ^ a := Nat.one_le_pow _ _ hl0
    have e2 : 1 ≤ l ^ (a + 1) := Nat.one_le_pow _ _ hl0
    have e3 : 1 ≤ l ^ (a + 1 + 1) := Nat.one_le_pow _ _ hl0
    have hn : l ^ (a + 1 + 1) - 1 = (l - 1) + l * (l ^ (a + 1) - 1) := by
      zify [e2, e3, (by omega : 1 ≤ l)]
      ring
    have hk : l ^ (a + 1) - 1 = (l - 1) + l * (l ^ a - 1) := by
      zify [e1, e2, (by omega : 1 ≤ l)]
      ring
    have hnk : (l ^ (a + 1 + 1) - 1).choose (l ^ (a + 1) - 1) =
        ((l - 1) + l * (l ^ (a + 1) - 1)).choose ((l - 1) + l * (l ^ a - 1)) := by
      rw [← hk, ← hn]
    rw [hnk]
    refine Choose.choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, Nat.add_mul_div_left _ _ hl0,
      Nat.div_eq_of_lt hlt, zero_add, Nat.choose_self, one_mul]
    exact ih

theorem primeDvdChooseIff : BinomGcd := by
  intro l hl n hn
  haveI := Fact.mk hl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨k, hk0, hkn, hndvd⟩ ⟨e, rfl⟩
    exact hndvd (hl.dvd_choose_pow (by omega) (by omega))
  · intro hnp
    have hd1 : l ^ padicValNat l n ∣ n := pow_padicValNat_dvd
    have hd2 : ¬ l ^ (padicValNat l n + 1) ∣ n := pow_succ_padicValNat_not_dvd (by omega)
    generalize padicValNat l n = v at hd1 hd2
    obtain ⟨m, rfl⟩ := hd1
    have hlm : ¬ l ∣ m := by
      rintro ⟨c, rfl⟩
      exact hd2 ⟨c, by ring⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hn
      omega
    have hm1 : m ≠ 1 := fun h => hnp ⟨v, by rw [h, mul_one]⟩
    have hp : 0 < l ^ v := pow_pos hl.pos v
    refine ⟨l ^ v, hp, lt_mul_of_one_lt_right hp (by omega), ?_⟩
    intro hd
    apply hlm
    exact Nat.modEq_zero_iff_dvd.1
      ((binomGcd_lucas_lemma l m v).symm.trans (Nat.modEq_zero_iff_dvd.2 hd))
  · intro e he hne
    subst hne
    obtain ⟨a, rfl⟩ : ∃ a, e = a + 1 := ⟨e - 1, by omega⟩
    refine ⟨l ^ a, pow_pos hl.pos a, Nat.pow_lt_pow_right hl.one_lt (by omega), ?_⟩
    have h1 : 1 ≤ l ^ a := Nat.one_le_pow _ _ hl.pos
    have h2 : 1 ≤ l ^ (a + 1) := Nat.one_le_pow _ _ hl.pos
    have key := Nat.add_one_mul_choose_eq (l ^ (a + 1) - 1) (l ^ a - 1)
    simp only [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2] at key
    have hc : (l ^ (a + 1)).choose (l ^ a) = l * (l ^ (a + 1) - 1).choose (l ^ a - 1) := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hl.pos a)
      rw [← key, pow_succ]
      ring
    intro hdvd
    rw [hc, pow_two, Nat.mul_dvd_mul_iff_left hl.pos] at hdvd
    have h3 : l ∣ 1 := Nat.modEq_zero_iff_dvd.1
      ((binomGcd_lucas_lemma_2 l a).symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd))
    exact hl.one_lt.ne' (Nat.dvd_one.1 h3)

theorem padicValFactorialBounds : FactValBounds := by
  intro l hl N hN
  haveI := Fact.mk hl
  have key := sub_one_mul_padicValNat_factorial (p := l) N
  have hsN : (l.digits N).sum ≤ N := Nat.digit_sum_le l N
  have hne : l.digits N ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  have hs1 : 1 ≤ (l.digits N).sum := by
    have hpos : 0 < (l.digits N).getLast hne :=
      Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero l (by omega))
    have := List.le_sum_of_mem (List.getLast_mem hne)
    omega
  have hdig : (l.digits N).sum ≤ (Nat.log l N + 1) * (l - 1) := by
    have hlen := Nat.digits_len l N hl.one_lt (by omega)
    have := List.sum_le_card_nsmul (l.digits N) (l - 1)
      (fun x hx => by have := Nat.digits_lt_base hl.one_lt hx; omega)
    rwa [smul_eq_mul, hlen] at this
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hl1 : (0 : ℝ) < l - 1 := by linarith
  have e := congrArg (fun t : ℕ => (t : ℝ)) key
  simp only [Nat.cast_mul, Nat.cast_sub hsN, Nat.cast_sub hl.one_le, Nat.cast_one] at e
  have hs1R : (1 : ℝ) ≤ ((l.digits N).sum : ℝ) := by exact_mod_cast hs1
  have hdigR := (Nat.cast_le (α := ℝ)).2 hdig
  simp only [Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_add, Nat.cast_one] at hdigR
  have hlog : (Nat.log l N : ℝ) ≤ Real.logb l N := Real.natLog_le_logb N l
  constructor
  · have h : (N : ℝ) / ((l : ℝ) - 1) ≤ (padicValNat l N.factorial : ℝ) + ((Nat.log l N : ℝ) + 1) := by
      rw [div_le_iff₀ hl1]
      nlinarith
    linarith
  · rw [le_div_iff₀ hl1]
    nlinarith

lemma num_fact_add_q (a k : ℕ) :
    (((a + k).factorial : ℕ) : ℚ) = (a.factorial : ℚ) * ∏ j ∈ Finset.range k, ((a : ℚ) + j + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]
    push_cast
    ring

lemma prod_range_eq_factorial_mul_prod_Ico (m x : ℕ) :
    ∏ j ∈ Finset.range m, ((((m + 1) * x : ℕ) : ℚ) + j + 1) =
      (m.factorial : ℚ) * ∏ i ∈ Finset.Ico 1 (m + 1), (1 + ((m + 1 : ℕ) : ℚ) * (x : ℚ) / (i : ℚ)) := by
  rw [Finset.prod_Ico_eq_prod_range, show m + 1 - 1 = m by omega,
    ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma num_uFac_succ (m x : ℕ) :
    uFac (m + 1) (x + 1) = uFac (m + 1) x * (-(m.factorial : ℚ) *
      ∏ i ∈ Finset.Ico 1 (m + 1), (1 + ((m + 1 : ℕ) : ℚ) * (x : ℚ) / (i : ℚ))) := by
  unfold uFac
  rw [show (m + 1) * (x + 1) = (m + 1) * x + (m + 1) by ring, num_fact_add_q,
    Finset.prod_range_succ, prod_range_eq_factorial_mul_prod_Ico m x, Nat.factorial_succ x]
  have h1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((x : ℚ) + 1) ≠ 0 := by positivity
  have h3 : ((x.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem unitFactorialProd : UProduct := by
  intro l hl x
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction x with
  | zero => simp [uFac]
  | succ x ih =>
    rw [num_uFac_succ, ih, Finset.prod_range_succ, pow_succ]
    ring

lemma num_one_add_four_mul_le (v : ℕ) : 1 + 4 * v ≤ 5 ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    have := Nat.one_le_pow v 5 (by norm_num)
    omega

theorem logCoeffValuation : LogCoeffVal := by
  intro l hl hl5 s hs
  haveI := Fact.mk hl
  have hdvd : l ^ padicValNat l s ∣ s := pow_padicValNat_dvd
  have hle : l ^ padicValNat l s ≤ s := Nat.le_of_dvd (by omega) hdvd
  have h5 : 5 ^ padicValNat l s ≤ l ^ padicValNat l s := Nat.pow_le_pow_left hl5 _
  have h4 := num_one_add_four_mul_le (padicValNat l s)
  have hN : 1 + 4 * padicValNat l s ≤ s := by omega
  have hR : (1 : ℝ) + 4 * (padicValNat l s : ℝ) ≤ s := by exact_mod_cast hN
  have hl5R : (5 : ℝ) ≤ l := by exact_mod_cast hl5
  have h14 : 1 / ((l : ℝ) - 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

theorem shiftExponentIdentity : LemmaMExponent := by
  intro l hl s0
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hne : (l : ℝ) ^ 2 ≠ 1 := by nlinarith
  have hne' : (l : ℝ) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hne
  refine ⟨?_, ?_⟩
  · rw [geom_sum_eq hne, rho, ← pow_mul, pow_succ]
    field_simp
    ring
  · intro s
    rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
    congr 1
    exact Finset.sum_congr rfl fun t _ => by ring

lemma num_bern_real (a : ℝ) (ha : 1 ≤ a) (w : ℕ) : 1 + (w : ℝ) * (a - 1) ≤ a ^ w := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ a - 1 by linarith) w
  simpa using h

set_option maxHeartbeats 800000 in
theorem weightNumerics : LemmaMNumerics := by
  intro l hl i hi
  obtain ⟨k, rfl⟩ := hi
  have hL : (5 : ℝ) ≤ l := by exact_mod_cast hl
  set L : ℝ := (l : ℝ) with hLdef
  have hL2 : L ^ 2 - 1 ≠ 0 := by nlinarith
  have hρpos : 0 < rho l := by
    unfold rho
    apply div_pos one_pos
    nlinarith
  have hρeq : L ^ 2 * rho l = 1 + rho l := by
    unfold rho
    rw [← hLdef]
    field_simp
    ring
  have hk1 : 1 ≤ L ^ (2 * k) := one_le_pow₀ (by linarith)
  have hLi : L ≤ L ^ (2 * k + 1) := by rw [pow_succ]; nlinarith
  have hLipos : 0 < L ^ (2 * k + 1) := by positivity
  have hinv : (L ^ (2 * k + 1))⁻¹ ≤ L⁻¹ := inv_anti₀ (by linarith) hLi
  have hinv5 : L⁻¹ ≤ 5⁻¹ := inv_anti₀ (by norm_num) hL
  have hinvpos : 0 < (L ^ (2 * k + 1))⁻¹ := inv_pos.2 hLipos
  have h14 : 1 / (L - 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  refine ⟨hρeq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i' hi'
    obtain ⟨j, rfl⟩ : ∃ j, i' = j + 3 := ⟨i' - 3, by omega⟩
    push_cast
    have b := num_bern_real L (by linarith) j
    have e : L ^ (j + 3) * rho l = L ^ (j + 1) * (1 + rho l) := by rw [← hρeq]; ring
    have hp : 0 < L ^ (j + 1) := by positivity
    have h1 : (1 + j * (L - 1)) * L ≤ L ^ j * L := mul_le_mul_of_nonneg_right b (by linarith)
    have h3 : (0 : ℝ) ≤ j * (L * (L - 1) - 1) := mul_nonneg (Nat.cast_nonneg j) (by nlinarith)
    have h4 : L ^ (j + 1) ≤ L ^ (j + 1) * (1 + rho l) := by nlinarith
    have hpow : L ^ (j + 1) = L ^ j * L := pow_succ L j
    rw [e]
    nlinarith
  · intro i' hi'
    obtain ⟨j, rfl⟩ : ∃ j, i' = j + 2 := ⟨i' - 2, by omega⟩
    push_cast
    have b := num_bern_real L (by linarith) j
    have e : L ^ (j + 2) * rho l = L ^ j * (1 + rho l) := by rw [← hρeq]; ring
    have hpj : 0 < L ^ j := by positivity
    have hm := mul_pos hpj hρpos
    have h : (0 : ℝ) ≤ j * (L - 5) := mul_nonneg (Nat.cast_nonneg j) (by linarith)
    have h25 : L ^ j * 25 ≤ L ^ j * L ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hpj.le
    have hpow : L ^ (j + 2) = L ^ j * L ^ 2 := pow_add L j 2
    refine ⟨?_, ?_⟩
    · rw [e]
      nlinarith
    · nlinarith
  · have := mul_nonneg (by linarith : (0 : ℝ) ≤ L - 1) hρpos.le
    nlinarith
  · rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, ← pow_mul]
    have : L ^ (2 * k + 1) ≠ 0 := hLipos.ne'
    field_simp
    ring
  · linarith
  · linarith
  · have e8 : (1 : ℝ) / (8 * L) = L⁻¹ / 8 := by ring
    rw [e8]
    linarith
  · intro i' hi'
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < L - 1)]
    have b := num_bern_real L (by linarith) i'
    linarith
  · intro J v hJ hv
    dsimp only
    have hδ : 9 / 40 ≤ rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1) := by linarith
    have hJR : (2 : ℝ) ≤ J := by exact_mod_cast hJ
    refine ⟨?_, ?_⟩
    · intro hv0
      subst hv0
      have hprod : 0 ≤ ((J : ℝ) - 1) * (rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1)) :=
        mul_nonneg (by linarith) (by linarith)
      push_cast
      linarith
    · intro hv1
      obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      have h5 : 5 ^ (w + 1) ≤ l ^ (w + 1) := Nat.pow_le_pow_left (by omega) _
      have h4 := num_one_add_four_mul_le w
      have hps : 5 ^ (w + 1) = 5 ^ w * 5 := pow_succ 5 w
      have hJn : 20 * w + 5 ≤ J := by omega
      have hJr : 20 * (w : ℝ) + 5 ≤ J := by exact_mod_cast hJn
      have hprod : (20 * (w : ℝ) + 4) * (9 / 40) ≤
          ((J : ℝ) - 1) * (rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1)) :=
        mul_le_mul (by linarith) hδ (by norm_num) (by linarith)
      push_cast
      nlinarith

end Formalism.IncomingBounds
